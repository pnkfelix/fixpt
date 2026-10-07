//! Printing descriptions, in FX-87's notation.

use crate::ast::{Atom, Effect, Region, Ty, TyId};
use crate::check::Checker;

impl Checker {
    pub fn show_region(&self, r: Region) -> String {
        match r {
            Region::Const(s) => self.interner.name(s).to_string(),
            Region::Var(v) => self.interner.name(self.arena.dvar_name(v)).to_string(),
            Region::Frozen(None, false) => "const".to_string(),
            Region::Frozen(None, true) => "acyclic".to_string(),
            Region::Frozen(Some(p), finite) => {
                format!("({} {})", if finite { "acyclic" } else { "const" }, self.interner.name(self.arena.dvar_name(p)))
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
            Atom::Var(v) => return self.interner.name(self.arena.dvar_name(v)).to_string(),
            Atom::Spin => return "spin".to_string(),
            Atom::App(n) => {
                let (head, args) = self.arena.effect_apps.parts(n);
                let ds: Vec<String> = args.iter().map(|a| self.show_earg(a)).collect();
                return format!("({} {})", self.interner.name(self.arena.dvar_name(head)), ds.join(" "));
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
                        let n = self.interner.name(self.arena.dvar_name(*v)).to_string();
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
            Conv::Var(v) => self.interner.name(self.arena.dvar_name(v)).to_string(),
        }
    }

    /// `pure`, a single atom, or `(maxeff …)`.
    /// Reads, or writes, of several globals are one atom: `(read (globals f
    /// g))`.
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
        self.show_ty_on(t, &mut Vec::new())
    }

    /// A type written out one level, even if it has a name: what a
    /// `define-type` defined the name as.
    pub fn show_definition(&self, t: TyId) -> String {
        self.show_ty_body(self.arena.resolve(t), &mut Vec::new())
    }

    fn abbreviation(&self, t: TyId) -> Option<&str> {
        let named = self.print_names.borrow().iter().rev().find(|(_, x)| self.arena.resolve(*x) == t).map(|(n, _)| *n);
        if let Some(n) = named {
            return Some(self.interner.name(n));
        }
        self.type_names()
            .into_iter()
            .rev()
            .find(|n| self.type_named(*n).is_some_and(|d| self.arena.resolve(d) == t))
            .map(|n| self.interner.name(n))
    }

    fn show_ty_on(&self, t: TyId, path: &mut Vec<TyId>) -> String {
        let t = self.arena.resolve(t);
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
            return format!("%{}", i + 1);
        }
        path.push(t);
        let name = format!("%{}", path.len());
        let out = match self.arena.get(t).clone() {
            Ty::Base(s) => self.interner.name(s).to_string(),
            Ty::Void => "void".into(),
            Ty::Var(v) => self.interner.name(self.arena.dvar_name(v)).to_string(),
            Ty::Link(None) => "?".into(),
            Ty::Link(Some(_)) => unreachable!("resolved"),
            Ty::Subr { conv, effect, params, result } => {
                let ps: Vec<String> = params.iter().map(|p| self.show_ty_on(*p, path)).collect();
                // The convention only where it is not the program's.
                let c = if conv == self.conv_default { String::new() } else { format!("(conv {}) ", self.show_conv(conv)) };
                format!("(subr {c}{} ({}) {})", self.show_effect(&effect), ps.join(" "), self.show_ty_on(result, path))
            }
            Ty::Poly { binders, body } => {
                let bs: Vec<String> = binders
                    .iter()
                    .map(|(v, k)| {
                        let k = self.show_kind(*k);
                        match self.arena.bound(*v) {
                            Some(b) => format!("({} {k} {})", self.interner.name(self.arena.dvar_name(*v)), self.show_region(b)),
                            None => format!("({} {k})", self.interner.name(self.arena.dvar_name(*v))),
                        }
                    })
                    .collect();
                format!("(poly ({}) {})", bs.join(" "), self.show_ty_on(body, path))
            }
            Ty::Ref(a, r) => format!("(ref {} {})", self.show_ty_on(a, path), self.show_region(r)),
            Ty::Module { abs, descs, vals } => {
                let mut out = String::from("(moduleof");
                for (n, v) in &abs {
                    let k = self.arena.dvar_kind_known(*v).unwrap_or(crate::ast::Kind::Type);
                    out.push_str(&format!(" (abs {} {})", self.interner.name(*n), self.show_kind(k)));
                }
                // Each description's name, after it, names what it is.
                let mark = self.print_names.borrow().len();
                for (n, x) in descs.iter() {
                    // An effect, a description function of no parameters.
                    let shown = match self.arena.get(self.arena.resolve(*x)) {
                        Ty::Lam { params, body: crate::ast::D::Effect(e) } if params.is_empty() => self.show_effect(e),
                        // What it is, not its own name: a `define-type` alias
                        // of it, `(select m n)`, named `n` too.
                        _ if self.abbreviation(self.arena.resolve(*x)) == Some(self.interner.name(*n)) => {
                            self.show_ty_body(self.arena.resolve(*x), path)
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
                out.push(')');
                out
            }
            Ty::Select(m, n) => format!("(select {} {})", self.interner.name(m), self.interner.name(n)),
            Ty::ParamSel(k, n) => format!("(select ${} {})", k + 1, self.interner.name(n)),
            Ty::Product(parts) | Ty::Sum(parts) => {
                let head = if matches!(self.arena.get(t), Ty::Product(_)) { "productof" } else { "sumof" };
                let ps: Vec<String> =
                    parts.iter().map(|(l, x)| format!(" ({} {})", self.interner.name(*l), self.show_ty_on(*x, path))).collect();
                format!("({head}{})", ps.concat())
            }
            Ty::Array(a, r) => format!("(arrayof {} {})", self.show_ty_on(a, path), self.show_region(r)),
            Ty::ICell(a, r) => format!("(icell {} {})", self.show_ty_on(a, path), self.show_region(r)),
            Ty::Place(r) => format!("(place {})", self.show_region(r)),
            Ty::Nat(crate::ast::Size::Finite) => "nat".to_string(),
            Ty::Nat(size) => format!("(nat {})", self.show_size(&size)),
            // FX-87's `listof`: a pair whose tail is itself.
            Ty::Pair(a, b, r, true) if self.arena.resolve(b) == t => {
                format!("(listof {} {})", self.show_ty_on(a, path), self.show_region(r))
            }
            Ty::PromptTag { answer, payload, effect, region } => format!(
                "(prompt-tag {} {} {} {})",
                self.show_ty_on(answer, path),
                self.show_ty_on(payload, path),
                self.show_effect(&effect),
                self.show_region(region)
            ),
            Ty::Composable { arg, answer, effect, region } => format!(
                "(composable {} {} {} {})",
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
                    self.interner.name(self.arena.dvar_name(p))
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
                    params.iter().map(|(v, k)| format!("({} {})", self.interner.name(self.arena.dvar_name(*v)), self.show_kind(*k))).collect();
                format!("(dlambda ({}) {})", ps.join(" "), self.show_d_on(&body, path))
            }
            Ty::Pair(a, b, r, nil) => {
                let pair = format!("(pairof {} {} {})", self.show_ty_on(a, path), self.show_ty_on(b, path), self.show_region(r));
                if nil { format!("(union nil {pair})") } else { pair }
            }
        };
        path.pop();
        if mentions_token(&out, &name) { format!("(mu {name} {out})") } else { out }
    }
}

/// Whether `name` occurs in `s` as a symbol of its own.
fn mentions_token(s: &str, name: &str) -> bool {
    ["(", " "].iter().any(|b| [")", " "].iter().any(|a| s.contains(&format!("{b}{name}{a}"))))
}
