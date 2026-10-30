//! Printing descriptions, in FX-87's notation.

use crate::ast::{Atom, Effect, Region, Ty, TyId};
use crate::check::Checker;
use std::collections::HashMap;

impl Checker {
    /// A product's or sum's label as a type shows it: a keyword, `#:name`
    /// (`docs/fx26.md`, "Keywords"); a number, which no keyword is, bare
    /// (as `check-print.fx`'s `k-label-shown`).
    pub(crate) fn show_label(&self, l: fixpt_read::Sym) -> String {
        let n = self.interner.name(l);
        if !n.is_empty() && n.bytes().all(|b| b.is_ascii_digit()) { n.to_string() } else { format!("#:{n}") }
    }

    /// Variable `v`'s name, or, while two types are shown apart
    /// ([`show_apart`](Self::show_apart)), a mark for it, named after: `f`
    /// where it is free, `b` where it is bound, `h` where it is bound and
    /// not printed (a `moduleof`'s abstract type, shown by its component's
    /// name).
    fn dvar_text(&self, v: crate::ast::DVar, how: char) -> String {
        if how == 'f'
            && let Some(shown) = self.print_for_fasl.borrow().as_ref().and_then(|m| m.get(&v).cloned())
        {
            return shown;
        }
        if self.show_marks.get() {
            format!("{MARK}{how}{}{MARK}", v.0)
        } else if how == 'h' {
            String::new()
        } else {
            self.interner.name(self.arena.dvar_name(v)).to_string()
        }
    }

    /// What `make` shows, with two free variables of one name told apart:
    /// the first, in the order the texts are read, keeps its name, the next
    /// is primed, `a'`, and so on; and a line for each such name saying so,
    /// or "". So that "a (subr pure (a) a) is expected here, and this is a
    /// (subr pure (a) a)" says which `a` is which.
    pub(crate) fn show_apart(&self, make: impl FnOnce(&Self) -> Vec<String>) -> (Vec<String>, String) {
        self.show_marks.set(true);
        let texts = make(self);
        self.show_marks.set(false);
        let marks: Vec<(char, u32)> = texts.iter().flat_map(|t| marks_in(t)).collect();
        let name = |v: u32| self.interner.name(self.arena.dvar_name(crate::ast::DVar(v))).to_string();
        // The free ones, by name, in the order they are read.
        let mut groups: Vec<(String, Vec<u32>)> = Vec::new();
        for &(how, v) in &marks {
            if how != 'f' || marks.iter().any(|&(h, w)| w == v && h != 'f') {
                continue;
            }
            let n = name(v);
            match groups.iter_mut().find(|(m, _)| *m == n) {
                Some((_, vs)) if !vs.contains(&v) => vs.push(v),
                Some(_) => {}
                None => groups.push((n, vec![v])),
            }
        }
        let mut primed: Vec<(u32, String)> = Vec::new();
        let mut hint = String::new();
        for (n, vs) in groups.iter().filter(|(_, vs)| vs.len() > 1) {
            let shown: Vec<String> = (0..vs.len()).map(|k| format!("{n}{}", "'".repeat(k))).collect();
            primed.extend(vs.iter().copied().zip(shown.iter().cloned()));
            let quoted: Vec<String> = shown.iter().map(|x| format!("`{x}`")).collect();
            let (last, init) = quoted.split_last().expect("two");
            hint.push_str(&format!("\n  {} and {last} are different variables, each named `{n}`", init.join(", ")));
        }
        let texts = texts
            .iter()
            .map(|t| {
                named_marks(t, |how, v| match how {
                    'h' => String::new(),
                    _ => primed.iter().find(|(w, _)| *w == v).map_or_else(|| name(v), |(_, x)| x.clone()),
                })
            })
            .collect();
        (texts, hint)
    }

    /// A proposition as written: `(shape 0 int)`, `(not (shape 0 int))`.
    pub(crate) fn show_prop(&self, p: &crate::ast::Prop) -> String {
        use crate::ast::{Prop, Rel, Term};
        let term = |t: &Term| match t {
            Term::Param(i) => i.to_string(),
            Term::Length(i) => format!("(length {i})"),
            Term::Lit(k) => format!("(lit {k})"),
        };
        match p {
            Prop::Shape { param, shape, negated } => {
                let shape = format!("(shape {param} {})", crate::check::SHAPES[*shape].0);
                if *negated { format!("(not {shape})") } else { shape }
            }
            Prop::Acyclic(i) => format!("(acyclic {i})"),
            Prop::Nat(i) => format!("(nat {i})"),
            Prop::Length(i, j) => format!("(length {i} {j})"),
            Prop::Rel { op, a, b } => {
                let (name, not) = match op {
                    Rel::Lt => ("<", false),
                    Rel::Le => ("<=", false),
                    Rel::Eq => ("=", false),
                    Rel::Ne => ("=", true),
                };
                let r = format!("({name} {} {})", term(a), term(b));
                if not { format!("(not {r})") } else { r }
            }
        }
    }

    pub fn show_region(&self, r: Region) -> String {
        match r {
            Region::Const(s) => self.interner.name(s).to_string(),
            Region::Var(v) => self.dvar_text(v, 'f'),
            Region::Frozen(None, false) => "const".to_string(),
            Region::Frozen(None, true) => "acyclic".to_string(),
            Region::Frozen(Some(p), finite) => {
                format!("({} {})", if finite { "acyclic" } else { "const" }, self.dvar_text(p, 'f'))
            }
            Region::Heap => "heap".to_string(),
            Region::Global(g) => format!("(globals {})", self.interner.name(g)),
            Region::Globals => "@globals".to_string(),
        }
    }

    fn show_earg(&self, a: &crate::ast::EArg) -> String {
        match a {
            crate::ast::EArg::Region(r) => self.show_region(*r),
            crate::ast::EArg::Effect(e) => self.show_effect(e),
            crate::ast::EArg::Size(z) => self.show_size(z),
            crate::ast::EArg::Conv(c) => self.show_conv(*c),
        }
    }

    pub fn show_atom(&self, a: Atom) -> String {
        let (op, r) = match a {
            Atom::Read(r) => ("read", r),
            Atom::Write(r) => ("write", r),
            Atom::Alloc(r) => ("alloc", r),
            Atom::Goto(r) => ("goto", r),
            Atom::Comefrom(r) => ("comefrom", r),
            Atom::Await(r) => ("await", r),
            Atom::Init(r) => ("init", r),
            Atom::Send(r) => ("send", r),
            Atom::Receive(r) => ("receive", r),
            Atom::Var(v) => return self.dvar_text(v, 'f'),
            Atom::Spin => return "spin".to_string(),
            Atom::Nondet => return "nondet".to_string(),
            Atom::Stage => return "stage".to_string(),
            Atom::Io(k) => return format!("(io {})", k.name()),
            Atom::App(n) => {
                let (head, args) = self.arena.effect_apps.parts(n);
                let ds: Vec<String> = args.iter().map(|a| self.show_earg(a)).collect();
                return format!("({} {})", self.dvar_text(head, 'f'), ds.join(" "));
            }
        };
        format!("({op} {})", self.show_region(r))
    }

    /// A size: `finite`, a literal, a variable, or `(+ …)` / `(- v k)`.
    pub fn show_size(&self, s: &crate::ast::Size) -> String {
        match s {
            crate::ast::Size::Finite => "finite".into(),
            crate::ast::Size::Lin { k, terms } => {
                let mut parts: Vec<String> = terms
                    .iter()
                    .map(|(v, c)| {
                        let n = self.dvar_text(*v, 'f');
                        if *c == 1 { n } else { format!("(* {c} {n})") }
                    })
                    .collect();
                match (parts.len(), *k) {
                    (0, k) => k.to_string(),
                    (1, 0) => parts.pop().expect("one"),
                    (1, k) if k < 0 => format!("(- {} {})", parts[0], -k),
                    (_, 0) => format!("(+ {})", parts.join(" ")),
                    (_, k) => format!("(+ {} {k})", parts.join(" ")),
                }
            }
        }
    }

    /// A convention as a program writes it.
    pub fn show_conv(&self, c: crate::ast::Conv) -> String {
        use crate::ast::Conv;
        match c {
            Conv::Cellular => "cellular".into(),
            Conv::Native => "native".into(),
            Conv::Fx => "fx".into(),
            Conv::Var(v) => self.dvar_text(v, 'f'),
        }
    }

    /// `pure`, a single atom, or `(maxeff …)`.
    /// Reads, or writes, of several globals are one atom: `(read (globals f
    /// g))`.
    /// A specification's clauses, each after a space, as a `subr` type
    /// writes them: `(requires p)`, `(ensures r q)`, those not `true`.
    pub fn show_spec(&self, spec: &crate::ast::Spec) -> String {
        use crate::ast::Named;
        let param = |i: usize| spec.params.get(i).copied().flatten().map_or(format!("${i}"), |s| self.interner.name(s).to_string());
        fn name(u: &Checker, spec: &crate::ast::Spec, n: &Named) -> String {
            let param = |i: usize| spec.params.get(i).copied().flatten().map_or(format!("${i}"), |s| u.interner.name(s).to_string());
            match *n {
            Named::Param(i) => param(i),
            Named::Result => spec.result.map_or("result".to_string(), |s| u.interner.name(s).to_string()),
            Named::Length(i) => format!("(length {})", param(i)),
            Named::Shape(i, k) => format!("(shape {} {})", param(i), crate::check::SHAPES[k].0),
            Named::Acyclic(i) => format!("(acyclic {})", param(i)),
            Named::Nat(i) => format!("(nat {})", param(i)),
            Named::LengthIs(i, j) => format!("(length-is {} {})", param(i), param(j)),
            Named::Call(g, ref xs) => {
                let xs: String = xs.iter().map(|x| format!(" {}", crate::logic::show_expr(x, &|n: &Named| name(u, spec, n)))).collect();
                format!("({}{xs})", u.interner.name(g))
            }
            }
        }
        let _ = param;
        let name = |n: &Named| name(self, spec, n);
        let mut out = String::new();
        if !spec.requires.trivial() {
            out += &format!(" (requires {})", crate::logic::show(&spec.requires, &name));
        }
        if !spec.ensures.trivial() {
            out += &format!(" (ensures {} {})", name(&Named::Result), crate::logic::show(&spec.ensures, &name));
        }
        out
    }

    pub fn show_effect(&self, e: &Effect) -> String {
        let mut atoms: Vec<String> = Vec::new();
        let (mut reads, mut writes) = (Vec::new(), Vec::new());
        for a in &e.0 {
            match a {
                Atom::Read(Region::Global(g)) => reads.push(self.interner.name(*g).to_string()),
                Atom::Write(Region::Global(g)) => writes.push(self.interner.name(*g).to_string()),
                _ => atoms.push(self.show_atom(*a)),
            }
        }
        for (op, mut gs) in [("read", reads), ("write", writes)] {
            gs.sort();
            if !gs.is_empty() {
                atoms.push(format!("({op} (globals {}))", gs.join(" ")));
            }
        }
        match atoms.len() {
            0 => "pure".into(),
            1 => atoms[0].clone(),
            _ => format!("(maxeff {})", atoms.join(" ")),
        }
    }

    /// A type. A type that `define-type` named prints as its name. Any other
    /// recursive type prints as far as its first repetition, which is shown
    /// as `…` — enough to read, and it always terminates.
    pub fn show_ty(&self, t: TyId) -> String {
        self.canonically(t, |c| c.show_ty_on(t, &mut Vec::new()))
    }

    /// A type written out one level, even if it has a name: what a
    /// `define-type` defined the name as.
    pub fn show_definition(&self, t: TyId) -> String {
        self.canonically(t, |c| c.show_ty_body(c.canon(c.arena.resolve(t)), &mut Vec::new()))
    }

    /// A digest of type `t`'s structure, for a definition's stamp
    /// (`Fx26Session::definition_stamps`): the same for a type inferred and
    /// for it read back from a `.fasl`, however each shares its parts or
    /// winds its cycles, since it is of the tree `t` unfolds to. Of its
    /// nodes' own parts (`ty_label`), their names as text, not as this
    /// process's numbers. Nothing printed, no name in scope looked for,
    /// which is what `show_ty` spends its time on.
    pub fn ty_digest(&self, t: TyId) -> u64 {
        use std::hash::{Hash, Hasher};
        let root = self.arena.resolve(t);
        let (mut order, mut index): (Vec<TyId>, crate::ast::TyMap<usize>) = (Vec::new(), Default::default());
        let mut kids: Vec<Vec<TyId>> = Vec::new();
        let mut todo = vec![root];
        while let Some(n) = todo.pop() {
            if index.contains_key(&n) {
                continue;
            }
            index.insert(n, order.len());
            order.push(n);
            let mut ks = Vec::new();
            self.each_ty_kid(n, |k| ks.push(self.arena.resolve(k)));
            todo.extend(ks.iter().rev());
            kids.push(ks);
        }
        let kids: Vec<Vec<usize>> = kids.iter().map(|ks| ks.iter().map(|k| index[k]).collect()).collect();
        let labels: Vec<u64> = order.iter().map(|n| self.ty_label(*n)).collect();
        if !has_cycle(&kids) {
            // A tree, maybe shared: each node's digest of its label and its
            // kids', each node once.
            fn merkle(i: usize, kids: &[Vec<usize>], labels: &[u64], memo: &mut [Option<u64>]) -> u64 {
                if let Some(d) = memo[i] {
                    return d;
                }
                let mut h = std::collections::hash_map::DefaultHasher::new();
                labels[i].hash(&mut h);
                for &k in &kids[i] {
                    merkle(k, kids, labels, memo).hash(&mut h);
                }
                let d = h.finish();
                memo[i] = Some(d);
                d
            }
            return merkle(0, &kids, &labels, &mut vec![None; order.len()]);
        }
        // A cycle: the minimal graph (as `minimal_classes`), its classes
        // numbered as a walk from the root first meets them, each class's
        // label and its kids' numbers.
        let mut class: Vec<usize> = numbered(labels.iter());
        let mut count = class.iter().max().map_or(0, |m| m + 1);
        loop {
            let keys: Vec<(usize, Vec<usize>)> = (0..order.len()).map(|i| (class[i], kids[i].iter().map(|k| class[*k]).collect())).collect();
            let next = numbered(keys.iter());
            let n = next.iter().max().map_or(0, |m| m + 1);
            class = next;
            if n == count {
                break;
            }
            count = n;
        }
        let mut first: HashMap<usize, usize> = HashMap::new();
        for (i, c) in class.iter().enumerate() {
            first.entry(*c).or_insert(i);
        }
        let mut h = std::collections::hash_map::DefaultHasher::new();
        let mut number: HashMap<usize, usize> = HashMap::from([(class[0], 0)]);
        let mut queue = std::collections::VecDeque::from([class[0]]);
        while let Some(c) = queue.pop_front() {
            let i = first[&c];
            labels[i].hash(&mut h);
            for &k in &kids[i] {
                let n = number.len();
                let k = *number.entry(class[k]).or_insert_with(|| {
                    queue.push_back(class[k]);
                    n
                });
                k.hash(&mut h);
            }
        }
        h.finish()
    }

    /// A digest of node `t`'s own part, its kids aside (`ty_digest`).
    fn ty_label(&self, t: TyId) -> u64 {
        use crate::ast::D;
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        let name = |s: fixpt_read::Sym| self.interner.name(s);
        let var = |v: crate::ast::DVar| self.interner.name(self.arena.dvar_name(v));
        let d = |x: &D, h: &mut std::collections::hash_map::DefaultHasher| match x {
            D::Type(_) => 0.hash(h),
            D::Fun(_) => 1.hash(h),
            D::Region(r) => (2, self.show_region(*r)).hash(h),
            D::Effect(e) => (3, self.show_effect(e)).hash(h),
            D::Size(z) => (4, self.show_size(z)).hash(h),
            D::Conv(c) => (5, self.show_conv(*c)).hash(h),
        };
        let ty = self.arena.get(t);
        std::mem::discriminant(ty).hash(&mut h);
        match ty {
            Ty::Base(s) => name(*s).hash(&mut h),
            Ty::Void | Ty::Nil | Ty::False | Ty::Link(_) => {}
            Ty::Union(ms) => ms.len().hash(&mut h),
            Ty::Var(v) => var(*v).hash(&mut h),
            Ty::Subr { conv, effect, params, spec, .. } => {
                (self.show_conv(*conv), self.show_effect(effect), params.len()).hash(&mut h);
                if let Some(spec) = spec {
                    (self.show_spec(spec), spec.params.iter().map(|p| p.map(name)).collect::<Vec<_>>(), spec.result.map(name)).hash(&mut h);
                }
            }
            Ty::Poly { binders, .. } => {
                for (v, k) in binders {
                    (var(*v), self.show_kind(*k), self.arena.is_distinct(*v), self.arena.bound(*v).map(|b| self.show_region(b))).hash(&mut h);
                }
            }
            Ty::Ref(_, r) | Ty::ICell(_, r) | Ty::MarkKey(_, r) | Ty::Pair(_, _, r, false) | Ty::Place(r) => self.show_region(*r).hash(&mut h),
            Ty::Pair(_, _, r, true) => (self.show_region(*r), true).hash(&mut h),
            Ty::Array(_, z, r) => (self.show_size(z), self.show_region(*r)).hash(&mut h),
            Ty::Nat(z) => self.show_size(z).hash(&mut h),
            Ty::NList { size, region, .. } => (self.show_size(size), self.show_region(*region)).hash(&mut h),
            Ty::Bloblet { fields, frozen, region } => (fields.len(), frozen, self.show_region(*region)).hash(&mut h),
            Ty::PromptTag { effect, region, .. } => (self.show_effect(effect), self.show_region(*region)).hash(&mut h),
            Ty::Composable { effect, region, once, .. } => (self.show_effect(effect), self.show_region(*region), once).hash(&mut h),
            Ty::Product(ps) | Ty::Sum(ps) => ps.iter().for_each(|(l, _)| name(*l).hash(&mut h)),
            Ty::Named { which, args } => {
                name(self.generatives[*which as usize].name).hash(&mut h);
                args.iter().for_each(|x| d(x, &mut h));
            }
            Ty::App { args, .. } => args.iter().for_each(|x| d(x, &mut h)),
            Ty::Lam { params, body } => {
                params.iter().for_each(|(v, k)| (var(*v), self.show_kind(*k)).hash(&mut h));
                d(body, &mut h);
            }
            Ty::Module { abs, descs, vals } => {
                for (n, v) in abs {
                    (name(*n), self.arena.dvar_kind_known(*v).map(|k| self.show_kind(k))).hash(&mut h);
                }
                descs.iter().chain(vals).for_each(|(l, _)| name(*l).hash(&mut h));
                descs.len().hash(&mut h);
            }
            Ty::Select(m, n) => (name(*m), name(*n)).hash(&mut h),
            Ty::ParamSel(k, n) => (k, name(*n)).hash(&mut h),
        }
        h.finish()
    }

    /// What `show` prints of `t`, each node it reaches printed as its class
    /// in `t`'s minimal graph (`print_canon`), if `t` has a cycle and is
    /// the outermost type being printed.
    fn canonically(&self, t: TyId, show: impl FnOnce(&Self) -> String) -> String {
        // The modules' descriptions in scope, gathered once for the type.
        if self.print_selects.borrow().is_none() && self.print_for_fasl.borrow().is_none() {
            *self.print_selects.borrow_mut() = Some(self.module_selects());
            let out = self.canonically(t, show);
            *self.print_selects.borrow_mut() = None;
            return out;
        }
        if self.print_canon.borrow().is_some() || self.print_shallow.get() {
            return show(self);
        }
        let classes = self.minimal_classes(t);
        let set = classes.is_some();
        if set {
            *self.print_canon.borrow_mut() = classes;
        }
        let out = show(self);
        if set {
            *self.print_canon.borrow_mut() = None;
        }
        out
    }

    /// The descriptions of the modules bound in scope, each by its `select`
    /// (`(select m-buffer buffer)`), by shape (`shape_key`), the modules in
    /// the order they were bound, each's descriptions in order: so that a
    /// type of the structure of one is printed by it, not written out
    /// wherever each later module has it (`TODO.md` §138). The innermost
    /// binding of each name, not a standard one nor a hidden one (`%…`),
    /// nor the global whose line is printed (`print_self`); a description
    /// function, applied where it is used, not.
    fn module_selects(&self) -> HashMap<u64, Vec<(String, TyId)>> {
        let mut seen = std::collections::HashSet::new();
        let mut bound = Vec::new();
        for i in (self.standard_len..self.env.len()).rev() {
            let (n, t) = self.env[i];
            if seen.insert(n) {
                bound.push((n, t));
            }
        }
        let mut out: HashMap<u64, Vec<(String, TyId)>> = HashMap::new();
        for (n, t) in bound.into_iter().rev() {
            let name = self.interner.name(n);
            if name.starts_with('%') || Some(n) == self.print_self.get() {
                continue;
            }
            let Ty::Module { descs, .. } = self.arena.get(self.arena.resolve(t)) else { continue };
            for (d, x) in descs.iter() {
                let x = self.arena.resolve(*x);
                if self.abbreviates(x) && !matches!(self.arena.get(x), Ty::Lam { .. }) {
                    out.entry(self.shape_key(x)).or_default().push((format!("(select {name} {})", self.interner.name(*d)), x));
                }
            }
        }
        out
    }

    /// A key of `t`'s own part, the same for two types `same_ty` finds one:
    /// its kind, and its fields' or components' labels.
    fn shape_key(&self, t: TyId) -> u64 {
        use std::hash::{Hash, Hasher};
        let mut h = std::collections::hash_map::DefaultHasher::new();
        let ty = self.arena.get(self.arena.resolve(t));
        std::mem::discriminant(ty).hash(&mut h);
        match ty {
            Ty::Product(ps) | Ty::Sum(ps) => ps.iter().for_each(|(l, _)| l.hash(&mut h)),
            Ty::Module { descs, vals, .. } => descs.iter().chain(vals.iter()).for_each(|(l, _)| l.hash(&mut h)),
            Ty::Subr { params, .. } => params.len().hash(&mut h),
            _ => {}
        }
        h.finish()
    }

    /// Node `t` as its class's first, while a type is printed canonically.
    fn canon(&self, t: TyId) -> TyId {
        self.print_canon.borrow().as_ref().and_then(|m| m.get(&t).copied()).unwrap_or(t)
    }

    /// The classes of the nodes `t` reaches, those of its minimal graph
    /// (Moore's refinement: alike if their own parts print alike and their
    /// types are alike, in order), each node mapped to its class's first in
    /// a walk from `t`; none if `t` reaches no cycle, or no two are alike.
    fn minimal_classes(&self, t: TyId) -> Option<crate::ast::TyMap<TyId>> {
        let root = self.arena.resolve(t);
        let (mut order, mut index): (Vec<TyId>, crate::ast::TyMap<usize>) = (Vec::new(), Default::default());
        let mut kids: Vec<Vec<TyId>> = Vec::new();
        let mut todo = vec![root];
        while let Some(n) = todo.pop() {
            if index.contains_key(&n) {
                continue;
            }
            index.insert(n, order.len());
            order.push(n);
            let mut ks = Vec::new();
            self.each_ty_kid(n, |k| ks.push(self.arena.resolve(k)));
            todo.extend(ks.iter().rev());
            kids.push(ks);
        }
        let kids: Vec<Vec<usize>> = kids.iter().map(|ks| ks.iter().map(|k| index[k]).collect()).collect();
        if !has_cycle(&kids) {
            return None;
        }
        // A node printed by a name of its own (`print_tys`) is labelled by
        // it, so that it is not merged with one that is not.
        self.print_shallow.set(true);
        let labels: Vec<String> = order.iter().map(|n| self.print_tys.borrow().get(n).cloned().unwrap_or_else(|| self.show_ty_body(*n, &mut Vec::new()))).collect();
        self.print_shallow.set(false);
        let mut class: Vec<usize> = numbered(labels.iter());
        let mut count = class.iter().max().map_or(0, |m| m + 1);
        loop {
            let keys: Vec<(usize, Vec<usize>)> = (0..order.len()).map(|i| (class[i], kids[i].iter().map(|k| class[*k]).collect())).collect();
            let next = numbered(keys.iter());
            let n = next.iter().max().map_or(0, |m| m + 1);
            class = next;
            if n == count {
                break;
            }
            count = n;
        }
        if count == order.len() {
            return None;
        }
        let mut first: HashMap<usize, TyId> = HashMap::new();
        for (i, n) in order.iter().enumerate() {
            first.entry(class[i]).or_insert(*n);
        }
        Some(order.iter().enumerate().map(|(i, n)| (*n, first[&class[i]])).collect())
    }

    fn abbreviation(&self, t: TyId) -> Option<std::borrow::Cow<'_, str>> {
        // Written out, but for data that keeps its name (`closed_named`): a
        // recursive one would print with numbers by its depth (`mu %3`),
        // which would not read the same in two places.
        if self.print_expanded.get() && !self.closed_named.contains(&t) {
            return None;
        }
        // A name in scope abbreviates `t` if `t` is its type and has parts
        // to abbreviate (the user's, 2026-10-28): by structure, not by
        // which node was written with it, so that a checker that shares
        // equal nodes (`k-ty-new`) names alike (`k-alias-of`).
        let fits = |d: TyId| {
            let d = self.arena.resolve(d);
            self.abbreviates(d) && self.same_ty(d, t, &mut Vec::new())
        };
        let named = self.print_names.borrow().iter().rev().find(|(_, x)| fits(*x)).map(|(n, _)| *n);
        if let Some(n) = named {
            return Some(self.interner.name(n).into());
        }
        if !self.abbreviates(t) {
            return None;
        }
        // For a `.fasl`, only a name that means the same where it is read,
        // noted.
        if self.print_for_fasl.borrow().is_some() {
            let mut aliases = self.print_aliases.borrow_mut();
            let (allowed, used) = aliases.as_mut()?;
            let n = self.type_names().into_iter().rev().find(|n| allowed.contains(n) && self.type_named(*n).is_some_and(fits))?;
            if !used.contains(&n) {
                used.push(n);
            }
            return Some(self.interner.name(n).into());
        }
        if let Some(n) = self.type_names().into_iter().rev().find(|n| self.type_named(*n).is_some_and(fits)) {
            return Some(self.interner.name(n).into());
        }
        // A module's description in scope, by its `select` (`module_selects`).
        let selects = self.print_selects.borrow();
        let found = selects.as_ref()?.get(&self.shape_key(t))?.iter().find(|(_, x)| self.same_ty(*x, t, &mut Vec::new()));
        found.map(|(s, _)| s.clone().into())
    }

    /// Whether a type has parts, so that a name abbreviates it: not a base
    /// type, a variable, `nil`, `false` or `void`, each a word already.
    pub(crate) fn abbreviates(&self, t: TyId) -> bool {
        !matches!(self.arena.get(self.arena.resolve(t)), Ty::Base(_) | Ty::Var(_) | Ty::Nil | Ty::False | Ty::Void)
    }

    /// Whether `a` and `b` are one type by structure, following links: the
    /// same kind of node, the same regions, effects and sizes, and parts
    /// the same in order; a node of a kind not compared so (a `select`, a
    /// procedure with a specification, …) only itself. A pair met
    /// again is the same (`trail`). As `k-same-shape?`.
    pub(crate) fn same_ty(&self, a: TyId, b: TyId, trail: &mut Vec<(TyId, TyId)>) -> bool {
        let (a, b) = (self.arena.resolve(a), self.arena.resolve(b));
        if a == b || trail.contains(&(a, b)) {
            return true;
        }
        trail.push((a, b));
        let all = |xs: &[TyId], ys: &[TyId], trail: &mut Vec<(TyId, TyId)>| xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| self.same_ty(*x, *y, trail));
        let parts = |ps: &[(fixpt_read::Sym, TyId)], qs: &[(fixpt_read::Sym, TyId)], trail: &mut Vec<(TyId, TyId)>| {
            ps.len() == qs.len() && ps.iter().zip(qs).all(|((l, x), (m, y))| l == m && self.same_ty(*x, *y, trail))
        };
        match (self.arena.get(a).clone(), self.arena.get(b).clone()) {
            (Ty::Base(s), Ty::Base(u)) => s == u,
            (Ty::Var(v), Ty::Var(w)) => v == w,
            (Ty::Nil, Ty::Nil) | (Ty::False, Ty::False) | (Ty::Void, Ty::Void) => true,
            (Ty::Nat(m), Ty::Nat(n)) => m == n,
            (Ty::Subr { conv: c, effect: e, params: ps, result: r, spec: None }, Ty::Subr { conv: d, effect: f, params: qs, result: q, spec: None }) => {
                c == d && e == f && all(&ps, &qs, trail) && self.same_ty(r, q, trail)
            }
            (Ty::Poly { binders: bs, body: x }, Ty::Poly { binders: cs, body: y }) => bs == cs && self.same_ty(x, y, trail),
            (Ty::Ref(x, r), Ty::Ref(y, s)) => r == s && self.same_ty(x, y, trail),
            (Ty::Pair(x, xt, r, n), Ty::Pair(y, yt, s, m)) => r == s && n == m && self.same_ty(x, y, trail) && self.same_ty(xt, yt, trail),
            (Ty::Product(ps), Ty::Product(qs)) | (Ty::Sum(ps), Ty::Sum(qs)) => parts(&ps, &qs, trail),
            (Ty::Array(x, m, r), Ty::Array(y, n, s)) | (Ty::NList { elem: x, size: m, region: r }, Ty::NList { elem: y, size: n, region: s }) => {
                m == n && r == s && self.same_ty(x, y, trail)
            }
            (Ty::Named { which: g, args: xs }, Ty::Named { which: h, args: ys }) => {
                g == h
                    && xs.len() == ys.len()
                    && xs.iter().zip(&ys).all(|(x, y)| match (x, y) {
                        (crate::ast::D::Type(x), crate::ast::D::Type(y)) | (crate::ast::D::Fun(x), crate::ast::D::Fun(y)) => self.same_ty(*x, *y, trail),
                        (crate::ast::D::Region(r), crate::ast::D::Region(s)) => r == s,
                        (crate::ast::D::Effect(e), crate::ast::D::Effect(f)) => e == f,
                        (crate::ast::D::Size(m), crate::ast::D::Size(n)) => m == n,
                        (crate::ast::D::Conv(c), crate::ast::D::Conv(d)) => c == d,
                        _ => false,
                    })
            }
            (Ty::Union(ms), Ty::Union(ns)) => all(&ms, &ns, trail),
            // The same abstract types (binders), descriptions and values, as
            // the FX-26 checker interns a module's type (`k-ty-same?`).
            (Ty::Module { abs: aa, descs: ad, vals: av }, Ty::Module { abs: ba, descs: bd, vals: bv }) => aa == ba && parts(&ad, &bd, trail) && parts(&av, &bv, trail),
            _ => false,
        }
    }

    fn show_ty_on(&self, t: TyId, path: &mut Vec<TyId>) -> String {
        if self.print_shallow.get() {
            return "·".into();
        }
        let t = self.arena.resolve(t);
        if let Some(shown) = self.print_tys.borrow().get(&t) {
            return shown.clone();
        }
        let t = self.canon(t);
        if let Some(shown) = self.print_tys.borrow().get(&t) {
            return shown.clone();
        }
        if let Some(name) = self.abbreviation(t) {
            return name.to_string();
        }
        self.show_ty_body(t, path)
    }

    /// A description as written, inside a type being shown.
    fn show_d_on(&self, d: &crate::ast::D, path: &mut Vec<TyId>) -> String {
        match d {
            crate::ast::D::Type(x) | crate::ast::D::Fun(x) => self.show_ty_on(*x, path),
            crate::ast::D::Region(r) => self.show_region(*r),
            crate::ast::D::Effect(e) => self.show_effect(e),
            crate::ast::D::Size(z) => self.show_size(z),
            crate::ast::D::Conv(c) => self.show_conv(*c),
        }
    }

    fn show_ty_body(&self, t: TyId, path: &mut Vec<TyId>) -> String {
        // A node met again on the way down is a cycle: named by its depth,
        // and written `(mu %d …)` where the cycle starts.
        if let Some(i) = path.iter().position(|x| *x == t) {
            // Written out for `type-at`: by its distance up, so that a
            // recursive type reads the same wherever it is printed.
            if self.print_expanded.get() {
                self.print_cycles.borrow_mut().insert(i);
                return format!("%^{}", path.len() - i);
            }
            return format!("%{}", i + 1);
        }
        path.push(t);
        let name = format!("%{}", path.len());
        let out = match self.arena.get(t).clone() {
            Ty::Base(s) => self.interner.name(s).to_string(),
            Ty::Void => "void".into(),
            Ty::Nil => "nil".into(),
            Ty::False => "false".into(),
            Ty::Union(ms) => {
                let ms: Vec<String> = ms.iter().map(|m| self.show_ty_on(*m, path)).collect();
                format!("(union {})", ms.join(" "))
            }
            Ty::Var(v) => self.dvar_text(v, 'f'),
            Ty::Link(None) => "?".into(),
            Ty::Link(Some(_)) => unreachable!("resolved"),
            Ty::Subr { conv, effect, params, result, spec } => {
                let fasl = self.print_for_fasl.borrow().is_some();
                let depth = self.print_subrs.get() + 1;
                self.print_subrs.set(depth);
                let mut ps: Vec<String> = params.iter().map(|p| self.show_ty_on(*p, path)).collect();
                // The convention only where it is not the program's.
                let c = if conv == self.conv_default { String::new() } else { format!("(conv {}) ", self.show_conv(conv)) };
                // What a `bool` result proves, `(bool (then …) (else …))`,
                // as written; a specification's parameters by their names,
                // where it has clauses, and its clauses after the result.
                let mut clauses = String::new();
                let mut shown = self.show_ty_on(result, path);
                if let Some(spec) = &spec {
                    let mut spec = (**spec).clone();
                    if let Some((then, els, rest)) = crate::specs::latent_split(&spec.ensures) {
                        let side = |c: &Self, which: &str, ps: &[crate::ast::Prop]| format!("({which}{})", ps.iter().map(|p| format!(" {}", c.show_prop(p))).collect::<String>());
                        shown = format!("(bool {} {})", side(self, "then", &then), side(self, "else", &els));
                        spec.ensures = rest;
                    }
                    clauses = self.show_spec(&spec);
                    if !clauses.is_empty() {
                        for (p, n) in ps.iter_mut().zip(&spec.params) {
                            if let Some(n) = n {
                                *p = format!("({} : {p})", self.interner.name(*n));
                            }
                        }
                    }
                }
                self.print_subrs.set(depth - 1);
                // For a `.fasl`: the outermost one's parameters named, where
                // a type in it selects from one (`Ty::ParamSel`).
                let mark = "%p.";
                if fasl && depth == 1 && clauses.is_empty() && (ps.iter().any(|p| p.contains(mark)) || shown.contains(mark)) {
                    for (i, p) in ps.iter_mut().enumerate() {
                        *p = format!("({mark}{} : {p})", i + 1);
                    }
                }
                format!("(subr {c}{} ({}) {shown}{clauses})", self.show_effect(&effect), ps.join(" "))
            }
            Ty::Poly { binders, body } => {
                let bs: Vec<String> = binders
                    .iter()
                    .map(|(v, k)| {
                        let k = self.show_kind(*k);
                        let d = if self.arena.is_distinct(*v) { " distinct" } else { "" };
                        match self.arena.bound(*v) {
                            Some(b) => format!("({} {k} {}{d})", self.dvar_text(*v, 'b'), self.show_region(b)),
                            None => format!("({} {k}{d})", self.dvar_text(*v, 'b')),
                        }
                    })
                    .collect();
                format!("(poly ({}) {})", bs.join(" "), self.show_ty_on(body, path))
            }
            Ty::Ref(a, r) => format!("(ref {} {})", self.show_ty_on(a, path), self.show_region(r)),
            Ty::Module { abs, descs, vals } => {
                // For a `.fasl`, each abstract type named as its component,
                // which a restricted one's is not (`%hidden:t`).
                let renamed: Vec<_> = match self.print_for_fasl.borrow_mut().as_mut() {
                    Some(m) => abs.iter().map(|(n, v)| (*v, m.insert(*v, self.interner.name(*n).to_string()))).collect(),
                    None => Vec::new(),
                };
                let mut out = String::from("(moduleof");
                for (n, v) in &abs {
                    // Bound here, as a `poly`'s binders are.
                    let bound = self.dvar_text(*v, 'h');
                    let k = self.arena.dvar_kind_known(*v).unwrap_or(crate::ast::Kind::Type);
                    out.push_str(&format!(" (abs {}{bound} {})", self.interner.name(*n), self.show_kind(k)));
                }
                // Each description's name, after it, names what it is.
                let mark = self.print_names.borrow().len();
                for (n, x) in descs.iter() {
                    // An effect, a description function of no parameters.
                    let shown = match self.arena.get(self.arena.resolve(*x)) {
                        Ty::Lam { params, body: crate::ast::D::Effect(e) } if params.is_empty() => self.show_effect(e),
                        // A description function, as its `dlambda`: a name
                        // of one does not stand bare (`not_applied`).
                        Ty::Lam { params, .. } if !params.is_empty() => self.show_ty_body(self.canon(self.arena.resolve(*x)), path),
                        // What it is, not its own name: a `define-type` alias
                        // of it, `(select m n)`, named `n` too; nor a module's
                        // `select` (`module_selects`), which, of the module
                        // printed, would name it by itself. Its class's first
                        // node, as `show_ty_on` shows (`canon`).
                        _ if self
                            .abbreviation(self.arena.resolve(*x))
                            .is_some_and(|a| a == self.interner.name(*n) || a.starts_with("(select ")) =>
                        {
                            self.show_ty_body(self.canon(self.arena.resolve(*x)), path)
                        }
                        _ => self.show_ty_on(*x, path),
                    };
                    out.push_str(&format!(" (desc {} {shown})", self.interner.name(*n)));
                    self.print_names.borrow_mut().push((*n, *x));
                }
                for (n, x) in vals.iter() {
                    out.push_str(&format!(" (val {} {})", self.interner.name(*n), self.show_ty_on(*x, path)));
                }
                self.print_names.borrow_mut().truncate(mark);
                if let Some(m) = self.print_for_fasl.borrow_mut().as_mut() {
                    for (v, was) in renamed {
                        match was {
                            Some(w) => m.insert(v, w),
                            None => m.remove(&v),
                        };
                    }
                }
                out.push(')');
                out
            }
            Ty::Select(m, n) => format!("(select {} {})", self.interner.name(m), self.interner.name(n)),
            // A call takes apart every one in the types its procedure's
            // type has, however deep (`dependent_args`): the outermost
            // procedure's parameter.
            Ty::ParamSel(k, n) if self.print_for_fasl.borrow().is_some() => match self.print_params.borrow().as_ref().and_then(|ps| ps.get(k).cloned()) {
                Some(p) => format!("(select {p} {})", self.interner.name(n)),
                None => format!("(select %p.{} {})", k + 1, self.interner.name(n)),
            },
            Ty::ParamSel(k, n) => format!("(select ${} {})", k + 1, self.interner.name(n)),
            Ty::Product(parts) | Ty::Sum(parts) => {
                let head = if matches!(self.arena.get(t), Ty::Product(_)) { "productof" } else { "sumof" };
                let ps: Vec<String> = parts.iter().map(|(l, x)| format!(" ({} {})", self.show_label(*l), self.show_ty_on(*x, path))).collect();
                format!("({head}{})", ps.concat())
            }
            Ty::Array(a, crate::ast::Size::Finite, r) => format!("(arrayof {} {})", self.show_ty_on(a, path), self.show_region(r)),
            Ty::Array(a, n, r) => format!("(narrayof {} {} {})", self.show_ty_on(a, path), self.show_size(&n), self.show_region(r)),
            Ty::ICell(a, r) => format!("(icell {} {})", self.show_ty_on(a, path), self.show_region(r)),
            Ty::Place(r) => format!("(place {})", self.show_region(r)),
            Ty::Nat(crate::ast::Size::Finite) => "nat".to_string(),
            Ty::Nat(size) => format!("(nat {})", self.show_size(&size)),
            // FX-87's `listof`: a pair whose tail is itself. Not in a
            // label (`print_shallow`), which is the node's own part, so that a
            // list and a pair whose tail is that list (`nil` beside a pair,
            // in a join) are one class, and show alike.
            Ty::Pair(a, b, r, true) if !self.print_shallow.get() && self.canon(self.arena.resolve(b)) == t => {
                format!("(listof {} {})", self.show_ty_on(a, path), self.show_region(r))
            }
            Ty::PromptTag { answer, payload, effect, region } => format!(
                "(prompt-tag {} {} {} {})",
                self.show_ty_on(answer, path),
                self.show_ty_on(payload, path),
                self.show_effect(&effect),
                self.show_region(region)
            ),
            Ty::Composable { arg, answer, effect, region, once } => format!(
                "({} {} {} {} {})",
                if once { "oneshot" } else { "composable" },
                self.show_ty_on(arg, path),
                self.show_ty_on(answer, path),
                self.show_effect(&effect),
                self.show_region(region)
            ),
            Ty::MarkKey(x, r) => format!("(mark-key {} {})", self.show_ty_on(x, path), self.show_region(r)),
            Ty::Bloblet { fields, frozen, region } => {
                let fs: Vec<String> = fields.iter().map(|f| self.show_ty_on(*f, path)).collect();
                let head = if frozen { "frozen" } else { "fields" };
                let sep = if fs.is_empty() { "" } else { " " };
                format!("(bloblet ({head}{sep}{}) {})", fs.join(" "), self.show_region(region))
            }
            Ty::NList { elem, size, region } => match region {
                Region::Frozen(Some(p), _) => format!(
                    "(nlist {} {} {})",
                    self.show_ty_on(elem, path),
                    self.show_size(&size),
                    self.dvar_text(p, 'f')
                ),
                _ => format!("(nlist {} {})", self.show_ty_on(elem, path), self.show_size(&size)),
            },
            Ty::Named { which, args } => {
                let name = self.interner.name(self.generatives[which as usize].name).to_string();
                if args.is_empty() {
                    name
                } else {
                    let ds: Vec<String> = args.iter().map(|d| self.show_d_on(d, path)).collect();
                    format!("({name} {})", ds.join(" "))
                }
            }
            Ty::App { fun, args } => {
                let ds: Vec<String> = args.iter().map(|d| self.show_d_on(d, path)).collect();
                format!("({} {})", self.show_ty_on(fun, path), ds.join(" "))
            }
            Ty::Lam { params, body } => {
                let ps: Vec<String> =
                    params.iter().map(|(v, k)| format!("({} {})", self.dvar_text(*v, 'b'), self.show_kind(*k))).collect();
                format!("(dlambda ({}) {})", ps.join(" "), self.show_d_on(&body, path))
            }
            Ty::Pair(a, b, r, nil) => {
                let pair = format!("(pairof {} {} {})", self.show_ty_on(a, path), self.show_ty_on(b, path), self.show_region(r));
                if nil { format!("(union nil {pair})") } else { pair }
            }
        };
        path.pop();
        if self.print_expanded.get() {
            return if self.print_cycles.borrow_mut().remove(&path.len()) { format!("(mu {out})") } else { out };
        }
        if mentions_token(&out, &name) { format!("(mu {name} {out})") } else { out }
    }
}

/// What brackets a variable's mark in [`Checker::show_apart`]'s texts.
const MARK: char = '\u{1}';

/// The marks in `s`, in order: how each is printed, and its variable.
fn marks_in(s: &str) -> Vec<(char, u32)> {
    s.split(MARK).skip(1).step_by(2).filter_map(|m| Some((m.chars().next()?, m.get(1..)?.parse().ok()?))).collect()
}

/// `s` with each mark replaced by what `name` makes of it.
fn named_marks(s: &str, name: impl Fn(char, u32) -> String) -> String {
    s.split(MARK)
        .enumerate()
        .map(|(k, part)| match (k % 2, part.chars().next(), part.get(1..).and_then(|v| v.parse().ok())) {
            (1, Some(how), Some(v)) => name(how, v),
            _ => part.to_string(),
        })
        .collect()
}

/// Whether `name` occurs in `s` as a symbol of its own.
fn mentions_token(s: &str, name: &str) -> bool {
    ["(", " "].iter().any(|b| [")", " "].iter().any(|a| s.contains(&format!("{b}{name}{a}"))))
}

/// Whether the graph of `kids` (each node's successors) has a cycle.
fn has_cycle(kids: &[Vec<usize>]) -> bool {
    // 0 unseen, 1 on the way down, 2 done.
    let mut state = vec![0u8; kids.len()];
    for start in 0..kids.len() {
        if state[start] != 0 {
            continue;
        }
        let mut stack = vec![(start, 0usize)];
        state[start] = 1;
        while let Some((n, i)) = stack.pop() {
            if i < kids[n].len() {
                stack.push((n, i + 1));
                let k = kids[n][i];
                match state[k] {
                    1 => return true,
                    0 => {
                        state[k] = 1;
                        stack.push((k, 0));
                    }
                    _ => {}
                }
            } else {
                state[n] = 2;
            }
        }
    }
    false
}

/// Each of `xs` numbered by its first among them that is equal to it.
fn numbered<'a, T: Eq + std::hash::Hash + 'a>(xs: impl Iterator<Item = &'a T>) -> Vec<usize> {
    let mut seen: HashMap<&T, usize> = HashMap::new();
    xs.map(|x| {
        let n = seen.len();
        *seen.entry(x).or_insert(n)
    })
    .collect()
}
