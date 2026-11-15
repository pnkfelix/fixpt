//! A value lent to the thread for the length of a call: what a front end's
//! phase reads its heap through, so that the syntax it holds can be read
//! and made where it is, with no heap passed to every function on the way
//! (`docs/research/heap-syntax.md`). The pattern of the `scoped-tls` crate,
//! by type, in a stack.
//!
//! [`lend`] makes `&mut T` reachable, by [`with_lent`], for exactly the
//! call it is given, the lender's own reference unusable meanwhile (it is
//! borrowed by the call). A borrow inside a borrow of the same `T` is
//! refused, a panic, not a second `&mut`: so there is never more than one
//! live `&mut T` from a lending, as `RefCell` keeps it.

use std::any::TypeId;
use std::cell::Cell;

/// How many lendings may be inside one another on a thread.
const DEEPEST: usize = 16;

/// The lendings in force, innermost last, each its type, where it is (and
/// where its partner is, for a pair, [`lend_pair`]), and whether it is
/// borrowed now: a fixed stack of cells, so that a borrow is a look at a
/// few cells, no allocation and no `RefCell`. A pair lent with its first's
/// owner ([`lend_owned`]): `at` is the owner, its type `owner`, and
/// `project` finds the first in it at each borrow, as [`Project`] does.
struct Stack {
    depth: Cell<usize>,
    ty: [Cell<Option<TypeId>>; DEEPEST],
    at: [Cell<*mut ()>; DEEPEST],
    and: [Cell<*mut ()>; DEEPEST],
    borrowed: [Cell<bool>; DEEPEST],
    owner: [Cell<Option<TypeId>>; DEEPEST],
    project: [Cell<Option<Project>>; DEEPEST],
}

/// How a lending's owner gives the part of it lent: the owner, and the
/// owner's own function that finds it (`fn(&mut O) -> &mut A`, as a
/// pointer), to the part.
#[derive(Clone, Copy)]
struct Project(unsafe fn(*mut (), *const ()) -> *mut (), *const ());

/// [`Project`]'s first, for owner `O` and part `A`: `f` given `o`.
///
/// # Safety
/// `o` is a live `O`, borrowed for the call; `f` an `fn(&mut O) -> &mut A`.
unsafe fn project<O, A>(o: *mut (), f: *const ()) -> *mut () {
    // SAFETY: `f` was made of an `fn(&mut O) -> &mut A` (`lend_owned`), and
    // `o` is the live `O` its lending was given, borrowed now.
    let f: fn(&mut O) -> &mut A = unsafe { std::mem::transmute(f) };
    let o = unsafe { &mut *o.cast::<O>() };
    (f(o) as *mut A).cast()
}

thread_local! {
    static STACK: Stack = const {
        Stack {
            depth: Cell::new(0),
            ty: [const { Cell::new(None) }; DEEPEST],
            at: [const { Cell::new(std::ptr::null_mut()) }; DEEPEST],
            and: [const { Cell::new(std::ptr::null_mut()) }; DEEPEST],
            borrowed: [const { Cell::new(false) }; DEEPEST],
            owner: [const { Cell::new(None) }; DEEPEST],
            project: [const { Cell::new(None) }; DEEPEST],
        }
    };
}

/// Ends what [`lend`] began, however its call ends.
struct Unlend(usize);

impl Drop for Unlend {
    fn drop(&mut self) {
        STACK.with(|s| {
            s.ty[self.0].set(None);
            s.depth.set(self.0);
        });
    }
}

/// A lending of `ty`, at `at` and `and`, pushed: its place in the stack.
fn push(ty: TypeId, at: *mut (), and: *mut ()) -> usize {
    STACK.with(|s| {
        let d = s.depth.get();
        assert!(d < DEEPEST, "more than {DEEPEST} lendings inside one another");
        s.ty[d].set(Some(ty));
        s.at[d].set(at);
        s.and[d].set(and);
        s.borrowed[d].set(false);
        s.owner[d].set(None);
        s.project[d].set(None);
        s.depth.set(d + 1);
        d
    })
}

/// `t` lent to this thread while `f` runs: [`with_lent`] reaches it. A
/// lending of the same type inside this one hides this one until it ends.
pub fn lend<T: 'static, R>(t: &mut T, f: impl FnOnce() -> R) -> R {
    let _unlend = Unlend(push(TypeId::of::<T>(), (t as *mut T).cast(), std::ptr::null_mut()));
    f()
}

/// `a` and `b` lent together while `f` runs, as one lending of the pair
/// `(A, B)`: [`with_lent_pair`] reaches both by one look.
pub fn lend_pair<A: 'static, B: 'static, R>(a: &mut A, b: &mut B, f: impl FnOnce() -> R) -> R {
    let _unlend = Unlend(push(TypeId::of::<(A, B)>(), (a as *mut A).cast(), (b as *mut B).cast()));
    f()
}

/// `a`, which `owner` holds (`part` finds it there), and `b` lent together
/// while `f` runs, as [`lend_pair`] lends them; and `owner` too, by
/// [`with_owner`], to the code that runs inside: one lending, of one
/// borrow at a time, so that `a` and its owner are never both borrowed. The
/// part is found in the owner at each borrow, not kept apart from it.
pub fn lend_owned<O: 'static, A: 'static, B: 'static, R>(owner: &mut O, part: fn(&mut O) -> &mut A, b: &mut B, f: impl FnOnce() -> R) -> R {
    let k = push(TypeId::of::<(A, B)>(), (owner as *mut O).cast(), (b as *mut B).cast());
    let _unlend = Unlend(k);
    STACK.with(|s| {
        s.owner[k].set(Some(TypeId::of::<O>()));
        s.project[k].set(Some(Project(project::<O, A>, part as *const ())));
    });
    f()
}

/// `f` of the owner of the innermost lending of the pair `(A, B)`, if it
/// was lent with one of type `O` ([`lend_owned`]), borrowed for the call as
/// the pair is by [`with_lent_pair`]: none if that lending has no owner, or
/// a panic if none is lent or it is borrowed already.
pub fn with_owner<A: 'static, B: 'static, O: 'static, R>(f: impl FnOnce(&mut O) -> R) -> Option<R> {
    let ty = TypeId::of::<(A, B)>();
    let k = STACK.with(|s| {
        let mut k = s.depth.get();
        loop {
            if k == 0 {
                panic!("no {} is lent", std::any::type_name::<(A, B)>());
            }
            k -= 1;
            if s.ty[k].get() == Some(ty) {
                return k;
            }
        }
    });
    let (at, _unborrow) = STACK.with(|s| {
        if s.owner[k].get() != Some(TypeId::of::<O>()) {
            return None;
        }
        assert!(!s.borrowed[k].get(), "the {} lent is borrowed already", std::any::type_name::<(A, B)>());
        s.borrowed[k].set(true);
        Some((s.at[k].get(), Unborrow(k)))
    })?;
    // SAFETY: `at` is the `&mut O` given to `lend_owned`, whose call is
    // running, so the `O` is alive and its lender cannot use it meanwhile;
    // and `borrowed`, set until this call ends, keeps every other borrow of
    // this lending away: of the part (`with_lent_pair`, which finds it in
    // the owner) as of the owner.
    Some(f(unsafe { &mut *at.cast::<O>() }))
}

/// Clears the borrow [`borrow`] took, however its call ends.
struct Unborrow(usize);

impl Drop for Unborrow {
    #[inline(always)]
    fn drop(&mut self) {
        STACK.with(|s| s.borrowed[self.0].set(false));
    }
}

/// The innermost lending of type `ty`, borrowed: where it is, its partner,
/// and what ends the borrow. A panic if none is lent, or it is borrowed
/// already. Not generic, so a build that optimizes nothing makes it once.
#[inline(always)]
fn borrow(ty: TypeId, name: fn() -> &'static str) -> (*mut (), *mut (), Unborrow) {
    STACK.with(|s| {
        let mut k = s.depth.get();
        loop {
            if k == 0 {
                panic!("no {} is lent", name());
            }
            k -= 1;
            if s.ty[k].get() == Some(ty) {
                break;
            }
        }
        assert!(!s.borrowed[k].get(), "the {} lent is borrowed already", name());
        s.borrowed[k].set(true);
        let at = match s.project[k].get() {
            // SAFETY: an owner's lending (`lend_owned`): `at` is the owner,
            // alive while it runs, and borrowed now, by this borrow alone.
            Some(Project(p, f)) => unsafe { p(s.at[k].get(), f) },
            None => s.at[k].get(),
        };
        (at, s.and[k].get(), Unborrow(k))
    })
}

/// `f` of the `T` lent innermost ([`lend`]); a panic if none is lent, or
/// it is borrowed already (a `with_lent` of it inside one).
#[inline(always)]
pub fn with_lent<T: 'static, R>(f: impl FnOnce(&mut T) -> R) -> R {
    let (at, _, _unborrow) = borrow(TypeId::of::<T>(), std::any::type_name::<T>);
    // SAFETY: `at` is the `&mut T` given to `lend`, whose call is running
    // (its entry is cleared when it returns or unwinds, `Unlend`), so the
    // `T` is alive and its lender cannot use it meanwhile; and no other
    // `&mut T` from this lending is alive, `borrowed` refusing a second
    // until this one's call ends (`Unborrow`). A lending inside `f` of the
    // reference given to it reborrows it, which `lend`'s own borrow keeps
    // from being used meanwhile.
    let t = unsafe { &mut *at.cast::<T>() };
    f(t)
}

/// `f` of the pair lent innermost ([`lend_pair`]), as [`with_lent`].
#[inline(always)]
pub fn with_lent_pair<A: 'static, B: 'static, R>(f: impl FnOnce(&mut A, &mut B) -> R) -> R {
    let (at, and, _unborrow) = borrow(TypeId::of::<(A, B)>(), std::any::type_name::<(A, B)>);
    // SAFETY: as `with_lent`'s, for each of the two: `lend_pair` was given
    // two `&mut`, so they are distinct and both alive while it runs, and
    // `borrowed` keeps this the only borrow of them.
    let (a, b) = unsafe { (&mut *at.cast::<A>(), &mut *and.cast::<B>()) };
    f(a, b)
}

/// Whether a `T` is lent to this thread now.
pub fn is_lent<T: 'static>() -> bool {
    STACK.with(|s| (0..s.depth.get()).any(|k| s.ty[k].get() == Some(TypeId::of::<T>())))
}

/// Whether an `(A, B)` is lent to this thread now ([`lend_pair`]).
pub fn is_lent_pair<A: 'static, B: 'static>() -> bool {
    is_lent::<(A, B)>()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_lent_value_is_reached_and_given_back() {
        let mut n = 3u32;
        let r = lend(&mut n, || with_lent(|m: &mut u32| {
            *m += 1;
            *m * 10
        }));
        assert_eq!((r, n), (40, 4));
        assert!(!is_lent::<u32>());
    }

    #[test]
    #[should_panic(expected = "borrowed already")]
    fn a_borrow_inside_a_borrow_is_refused() {
        let mut n = 0u32;
        lend(&mut n, || with_lent(|_: &mut u32| with_lent(|_: &mut u32| ())));
    }

    #[test]
    fn an_inner_lending_hides_the_outer_until_it_ends() {
        let (mut a, mut b) = (1u32, 2u32);
        lend(&mut a, || {
            lend(&mut b, || assert_eq!(with_lent(|x: &mut u32| *x), 2));
            assert_eq!(with_lent(|x: &mut u32| *x), 1);
        });
    }

    #[test]
    fn a_pair_is_reached_by_one_borrow() {
        let (mut a, mut b) = (1u32, 'x');
        lend_pair(&mut a, &mut b, || with_lent_pair(|x: &mut u32, y: &mut char| {
            *x += 1;
            *y = 'y';
        }));
        assert_eq!((a, b), (2, 'y'));
        assert!(!is_lent_pair::<u32, char>());
    }

    struct Owner {
        part: u32,
        other: u32,
    }

    #[test]
    fn an_owned_part_and_its_owner_are_borrowed_in_turn() {
        let mut o = Owner { part: 1, other: 10 };
        let mut b = 'x';
        lend_owned(&mut o, |o: &mut Owner| &mut o.part, &mut b, || {
            with_lent_pair(|p: &mut u32, _: &mut char| *p += 1);
            let seen = with_owner::<u32, char, Owner, _>(|o| {
                o.other += o.part;
                o.part
            });
            assert_eq!(seen, Some(2));
            with_lent_pair(|p: &mut u32, _: &mut char| *p += 1);
        });
        assert_eq!((o.part, o.other), (3, 12));
    }

    #[test]
    #[should_panic(expected = "borrowed already")]
    fn the_owner_is_refused_while_its_part_is_borrowed() {
        let mut o = Owner { part: 1, other: 0 };
        let mut b = 'x';
        lend_owned(&mut o, |o: &mut Owner| &mut o.part, &mut b, || {
            with_lent_pair(|_: &mut u32, _: &mut char| with_owner::<u32, char, Owner, _>(|_| ()));
        });
    }

    #[test]
    fn a_lending_with_no_owner_gives_none() {
        let (mut a, mut b) = (1u32, 'x');
        lend_pair(&mut a, &mut b, || assert!(with_owner::<u32, char, Owner, _>(|_| ()).is_none()));
    }

    #[test]
    fn a_panic_inside_ends_the_lending() {
        let mut n = 0u32;
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| lend(&mut n, || with_lent(|_: &mut u32| panic!("inside")))));
        assert!(r.is_err());
        assert!(!is_lent::<u32>());
    }
}
