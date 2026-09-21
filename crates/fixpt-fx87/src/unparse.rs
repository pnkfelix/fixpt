//! Printing a description the way the reference prints it.
//!
//! This is not a debugging aid: the conformance goldens *are* this output, so
//! every parenthesis is a requirement. `unparse-dexp` is the function being
//! matched.
//!
//! # `dletrec`, and why it is needed
//!
//! FX-87 types can contain themselves. A list of integers is
//! `μX. (pairof int X @=)`, built by mutation in `type-check.lisp` and
//! perfectly finite as an object graph — but infinite to print naively.
//!
//! So a recursive occurrence is given a name and the whole thing is wrapped in
//! `dletrec`:
//!
//! ```text
//! (dletrec ((|#1| (pairof int |#1| @=))) (pairof int |#1| @=))
//! ```
//!
//! Note that the body and the binding print identically, because the type *is*
//! its own unrolling. The names are `|#1|`, `|#2|`, … in the order the cycles
//! are discovered, which is why the traversal order below is part of the
//! contract and not an implementation detail.
//!
//! The algorithm is the one the Scheme printer uses for `#n=` datum labels:
//! a depth-first walk with an on-path set, naming exactly the targets of back
//! edges. Sharing that is not a cycle is *not* named — an identical subtree
//! reached twice prints twice, as the reference does.

use crate::ast::{Arena, Desc, DescId, Kind};
use fixpt_read::{escape_symbol, Interner};
use std::collections::{HashMap, HashSet};

pub struct Printer<'a> {
    arena: &'a Arena,
    interner: &'a Interner,
    /// Recursive nodes and the name each was given.
    names: HashMap<DescId, String>,
    /// Which named nodes are currently being expanded, so a back edge prints
    /// the name rather than recurring forever.
    expanding: HashSet<DescId>,
}

/// Render `root` exactly as `unparse-dexp` would.
pub fn unparse(arena: &Arena, interner: &Interner, root: DescId) -> String {
    let mut names = HashMap::new();
    let mut order = Vec::new();
    find_cycles(arena, root, &mut Vec::new(), &mut HashSet::new(), &mut order);
    for (i, id) in order.iter().enumerate() {
        names.insert(*id, format!("#{}", i + 1));
    }
    let mut p = Printer { arena, interner, names, expanding: HashSet::new() };
    if order.is_empty() {
        return p.print(root);
    }
    // The bindings go *inside* any enclosing binder, because a recursive type
    // may mention a variable that binder introduces: `reverse` has type
    // `(poly ((r2 region)) (dletrec ((|#1| (pairof int |#1| r2))) …))`, and
    // hoisting the `dletrec` out would put `r2` out of scope.
    if let Desc::Poly { binders, body } = arena.get(root).clone() {
        let bs = p.binders(&binders);
        let inner = unparse(arena, interner, body);
        return format!("(poly ({bs}) {inner})");
    }
    let body = p.print(root);
    let bindings: Vec<String> = order
        .iter()
        .map(|id| {
            let name = escape_symbol(&p.names[id]);
            // Each binding expands its own node, so the recursive occurrence
            // inside prints as the name.
            let text = p.print_structure(*id);
            format!("({name} {text})")
        })
        .collect();
    format!("(dletrec ({}) {})", bindings.join(" "), body)
}

/// Collect the nodes that are targets of a back edge, in discovery order.
fn find_cycles(
    arena: &Arena,
    id: DescId,
    path: &mut Vec<DescId>,
    done: &mut HashSet<DescId>,
    order: &mut Vec<DescId>,
) {
    if path.contains(&id) {
        if !order.contains(&id) {
            order.push(id);
        }
        return;
    }
    // A node already fully explored cannot start a new cycle, but it can be
    // revisited as ordinary sharing — which is printed out in full, not named.
    if done.contains(&id) {
        return;
    }
    path.push(id);
    for child in children(arena, id) {
        find_cycles(arena, child, path, done, order);
    }
    path.pop();
    done.insert(id);
}

fn children(arena: &Arena, id: DescId) -> Vec<DescId> {
    match arena.get(id) {
        Desc::Var(_) | Desc::Pure | Desc::Hole => Vec::new(),
        Desc::Con(_, args) => args.clone(),
        Desc::Subr { effect, args, result } => {
            let mut v = vec![*effect];
            v.extend(args);
            v.push(*result);
            v
        }
        Desc::Vsubr { effect, args, rest, result } => {
            let mut v = vec![*effect];
            v.extend(args);
            v.push(*rest);
            v.push(*result);
            v
        }
        Desc::Poly { body, .. } | Desc::DAbs { body, .. } => vec![*body],
        Desc::RecordOf { fields, region } => {
            let mut v: Vec<DescId> = fields.iter().map(|(_, t)| *t).collect();
            v.push(*region);
            v
        }
        Desc::OneOf { variants, region } => {
            let mut v: Vec<DescId> = variants.iter().map(|(_, t)| *t).collect();
            v.push(*region);
            v
        }
        Desc::Read(r) | Desc::Write(r) | Desc::Alloc(r) => vec![*r],
        Desc::MaxEff(parts) | Desc::RUnion(parts) => parts.clone(),
        Desc::DApp { fun, args } => {
            let mut v = vec![*fun];
            v.extend(args);
            v
        }
    }
}

impl Printer<'_> {
    fn sym(&self, s: fixpt_read::Sym) -> String {
        escape_symbol(self.interner.name(s))
    }

    fn print(&mut self, id: DescId) -> String {
        if self.names.contains_key(&id) && self.expanding.contains(&id) {
            return escape_symbol(&self.names[&id]);
        }
        self.print_structure(id)
    }

    fn print_structure(&mut self, id: DescId) -> String {
        let named = self.names.contains_key(&id);
        if named {
            self.expanding.insert(id);
        }
        let out = self.structure(id);
        if named {
            self.expanding.remove(&id);
        }
        out
    }

    fn structure(&mut self, id: DescId) -> String {
        match self.arena.get(id).clone() {
            Desc::Var(s) => self.sym(s),
            Desc::Hole => "#<incomplete>".to_string(),
            Desc::Con(name, args) if args.is_empty() => self.sym(name),
            Desc::Con(name, args) => {
                let parts = self.list(&args);
                format!("({} {})", self.sym(name), parts)
            }
            Desc::Subr { effect, args, result } => {
                let e = self.print(effect);
                let a = self.list(&args);
                let r = self.print(result);
                format!("(subr {e} ({a}) {r})")
            }
            Desc::Vsubr { effect, args, rest, result } => {
                let e = self.print(effect);
                let mut parts = vec![e];
                for a in &args {
                    parts.push(self.print(*a));
                }
                parts.push(self.print(rest));
                parts.push(self.print(result));
                format!("(vsubr {})", parts.join(" "))
            }
            Desc::Poly { binders, body } => {
                let bs = self.binders(&binders);
                let b = self.print(body);
                format!("(poly ({bs}) {b})")
            }
            Desc::DAbs { binders, body } => {
                let bs = self.binders(&binders);
                let b = self.print(body);
                format!("(dlambda ({bs}) {b})")
            }
            Desc::RecordOf { fields, region } => {
                let f = self.named_fields(&fields);
                let r = self.print(region);
                format!("(recordof ({f}) {r})")
            }
            Desc::OneOf { variants, region } => {
                let f = self.named_fields(&variants);
                let r = self.print(region);
                format!("(oneof ({f}) {r})")
            }
            Desc::Pure => "pure".to_string(),
            Desc::Read(r) => format!("(read {})", self.print(r)),
            Desc::Write(r) => format!("(write {})", self.print(r)),
            Desc::Alloc(r) => format!("(alloc {})", self.print(r)),
            Desc::MaxEff(parts) => format!("(maxeff {})", self.list(&parts)),
            Desc::RUnion(parts) => format!("(runion {})", self.list(&parts)),
            Desc::DApp { fun, args } => {
                let f = self.print(fun);
                let a = self.list(&args);
                format!("({f} {a})")
            }
        }
    }

    fn list(&mut self, ids: &[DescId]) -> String {
        ids.iter().map(|d| self.print(*d)).collect::<Vec<_>>().join(" ")
    }

    fn named_fields(&mut self, fields: &[(fixpt_read::Sym, DescId)]) -> String {
        fields
            .iter()
            .map(|(n, t)| format!("({} {})", self.sym(*n), self.print(*t)))
            .collect::<Vec<_>>()
            .join(" ")
    }

    pub(crate) fn binders(&mut self, binders: &[crate::ast::Binder]) -> String {
        binders
            .iter()
            .map(|b| format!("({} {})", self.sym(b.name), print_kind(&b.kind)))
            .collect::<Vec<_>>()
            .join(" ")
    }
}

pub fn print_kind(k: &Kind) -> String {
    match k {
        Kind::Type | Kind::Effect | Kind::Region => k.name().to_string(),
        Kind::DFunc(args, result) => {
            let a: Vec<String> = args.iter().map(print_kind).collect();
            format!("(dfunc ({}) {})", a.join(" "), print_kind(result))
        }
    }
}
