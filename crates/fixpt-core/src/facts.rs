//! What a front end proved, carried alongside the code.
//!
//! # The problem
//!
//! A front end knows things the back end cannot recover. FX-87's checker
//! resolves every name to a binding, computes an effect for every expression,
//! and proves — by rejecting the programs where it fails — that a standard
//! binding can never be reassigned. Erasing to Scheme throws all of it away,
//! and the compiler then spends 42% of its instruction stream on call plumbing
//! it could have avoided.
//!
//! # Twobit's answer, and the part it left out
//!
//! Larceny's compiler faced the same problem and solved it in a way worth
//! copying. A Twobit `lambda` node is *literal Scheme*:
//!
//! ```scheme
//! (lambda (x)
//!   (begin defs …)
//!   '(R F G decls doc)      ; ← evaluated for effect, discarded
//!   body)
//! ```
//!
//! The analyses ride in body position as a quoted constant: inert, so any
//! conforming evaluator runs the program correctly and ignores them, and
//! durable, because they survive being written out and read back as ordinary
//! data. `pass2.aux.sch` even keeps the faster representation it *didn't* use
//! — `(vector lambda-tag …)` — commented out beside it, because that one would
//! no longer be Scheme.
//!
//! What Twobit never carried is the **justification**. `lambda.F` says `x` is
//! free; nothing can ask why, or notice when the analysis was wrong. The
//! specialised operator names have the same shape — `.+:fix:fix` asserts that
//! its arguments are fixnums and cannot be interrogated, so a bug in
//! representation inference flows silently into unchecked machine code.
//!
//! # What this adds
//!
//! The same encoding, plus the derivation. For a type checker the justification
//! is nearly free: it is the evidence the checker already built and was about
//! to discard. So a claim records *why* it holds and, crucially, **on what
//! basis** — see [`Basis`]. A fact that was checked by a type system and one
//! that an analysis guessed are both useful and are not the same thing, and a
//! compiler that cannot tell them apart has to treat the sound one as
//! suspiciously as the unsound one.

use fixpt_read::Sym;

/// How much weight a claim carries.
///
/// The distinction Twobit could not express. `.+:fix:fix` and a
/// programmer's `(declare (fixnum x))` look identical downstream, and one of
/// them is a proof obligation the compiler discharged while the other is a
/// promise nobody checked.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Basis {
    /// A type system rejects every program in which this is false. The strongest
    /// kind, and the one FX supplies as a byproduct of checking.
    Checked,
    /// An analysis pass derived it. Sound if the pass is, which is exactly the
    /// thing that cannot be assumed — Twobit's representation inference lives
    /// here, and so does its `FIXME`.
    Inferred,
    /// Someone asserted it. Believed, not verified.
    Asserted,
}

/// A single claim about one expression.
#[derive(Clone, PartialEq, Debug)]
pub enum Claim {
    /// Evaluating this has no observable effect: it may be dropped when its
    /// value is unused, reordered against other pure expressions, or shared
    /// with an equal one.
    Pure,
    /// The operator of this application is a primitive that cannot be rebound,
    /// so the call may be compiled without the indirection through a global.
    ///
    /// Sound in FX-87 because assigning a standard binding is a *type error* —
    /// they live in the immutable region — and unsound in Scheme for exactly
    /// the reason it is not: `(set! + -)` is an ordinary program there.
    Integrable(Sym),
    /// Nothing this expression allocates outlives it, so it needs no
    /// safepoint and could in principle be stack-allocated. In FX this falls
    /// out of effect masking, which is an escape analysis the checker has
    /// already run.
    NoEscape,
}

/// A claim, why it holds, and how far it can be trusted.
#[derive(Clone, PartialEq, Debug)]
pub struct Fact {
    pub claim: Claim,
    pub basis: Basis,
    /// The derivation, verbatim from the front end — for FX, the type or effect
    /// the checker used. Kept as text rather than parsed: nothing here consumes
    /// it yet, and the point is that a *later* verifier could, without the
    /// front end having to anticipate what that verifier wants.
    pub because: Option<String>,
}

impl Fact {
    pub fn checked(claim: Claim, because: impl Into<String>) -> Fact {
        Fact { claim, basis: Basis::Checked, because: Some(because.into()) }
    }
}

/// Facts about one expression. Most expressions have none.
#[derive(Clone, Default, PartialEq, Debug)]
pub struct Facts(pub Vec<Fact>);

impl Facts {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn has(&self, claim: &Claim) -> bool {
        self.0.iter().any(|f| f.claim == *claim)
    }

    /// The primitive this application may be compiled as, if any.
    pub fn integrable(&self) -> Option<Sym> {
        self.0.iter().find_map(|f| match f.claim {
            Claim::Integrable(s) => Some(s),
            _ => None,
        })
    }

    pub fn is_pure(&self) -> bool {
        self.has(&Claim::Pure)
    }

    /// Only facts a compiler may act on without further argument.
    ///
    /// A `Checked` fact is as good as the front end's type system; the others
    /// are worth keeping — a debug build could insert the runtime test that
    /// `Twobit` had no way to ask for — but are not licence to remove code.
    pub fn trusted(&self) -> impl Iterator<Item = &Fact> {
        self.0.iter().filter(|f| f.basis == Basis::Checked)
    }
}
