# KFX26: a kernel of FX-26 for one front end, two targets

A short note, 2026-10-02, from a discussion with the user; nothing is
built. The user's idea: a kernel sublanguage of FX-26, *KFX26*, in which
the language implementation (parsing, static analysis, code generation)
is written once, and which maps straightforwardly (with annotations in
types or comments where needed) both to FX-26 itself and to
semi-idiomatic Rust; lowering to Scheme too, but that matters less.

## Why

Today the two checkers, and the two compilers, are written twice and
kept in step by hand, "rule for rule, message for message", with tests
comparing them word for word. Every feature of the past week was built
twice: modules' stages M1–M7 (`first-class-modules.md`), tail calls in
leaves, the hole hints. One KFX26 source producing both would remove
the doubling; the agreement tests would become tests of the translation.

## Higher kinds, as Rust's generic associated types

Rust has no general higher-kinded types, but it has generic associated
types (GATs), which are the restricted form `higher-kinds.md` calls Path
2: an abstract type constructor as a component of an interface, applied
where it is declared. The correspondence (the user's motivation for
asking about `type -> type`):

| Rust                                                 | FX-26, Path 2                                                              |
| ---------------------------------------------------- | -------------------------------------------------------------------------- |
| a trait with `type Pointer<T>;`                      | a `moduleof` with `(abs pointer (=> (type) type))`                         |
| an `impl` of the trait                               | a module                                                                   |
| `fn f<P: PointerFamily>(…)` using `P::Pointer<u8>`   | a dependent procedure on a module parameter, `(select $1 pointer)` at `u8` |
| `type Item<'a> where Self: 'a;` (a lending iterator) | an abstract component of kind region → type: regions as lifetimes          |

So KFX26 keeps higher kinds in Path 2's shape only: abstract type
constructors as module components, applied where declared (the scoped
rule of `higher-kinds.md`'s open question 2, which is what keeps the
mapping to GATs direct). It leaves out Path 1's free-standing `(poly ((f
(=> (type) type))) …)`, which Rust cannot say. The lending iterator wants
kind region → type, which brings in the question, deferred so far, of
abstract region components (`higher-kinds.md`, open question 3;
`first-class-modules.md`, "later").

## How FX-26 maps to Rust

As the front end uses each:

| FX-26                                        | Rust                                                   | how hard                                                                  |
| -------------------------------------------- | ------------------------------------------------------ | ------------------------------------------------------------------------- |
| products, sums, `tagcase`                    | structs, enums, `match`                                | direct                                                                    |
| `define-generative`                          | newtypes                                               | direct                                                                    |
| recursive types                              | named enums with `Box`/`Vec`, or arena indices         | nominal only: KFX26 forbids anonymous `mu`                                |
| state in a region (`@t`, `@k`; refs, arrays) | a state struct, passed `&mut`; arenas with index types | the main decision; the Rust checker's `Arena` and `TyId` are the shape    |
| effects (`kstate`, `checks`, …)              | erased, or as that `&mut` parameter                    | annotations only                                                          |
| `k-fail`: an abort to the error prompt       | `Result` and `?`                                       | a rule: the kernel's only control is that abort                           |
| continuations, `cwcc`, marks                 | none                                                   | not in the kernel                                                         |
| `poly` over types                            | generics, monomorphized                                | first-order only                                                          |
| `poly` over regions and effects              | lifetimes, or erased                                   | mostly erased                                                             |
| closures                                     | closures; `fn` items where nothing is captured         | what they capture, and its ownership, is the hard part: restrict captures |
| lists (`listof … @t`)                        | `Vec`, or a persistent list                            | choose one                                                                |
| modules                                      | Rust modules; functors as generic structs or traits    | first-order modules map well; dependent procedures less so                |
| `spin`, sizes, termination                   | erased                                                 | free                                                                      |
| ref hooks (`c-register-code`, …)             | `fn` pointers in the state struct                      | direct                                                                    |

## Decisions to make first

1. **The memory model.** Trees as immutable values (`Rc` or `Box` in
   Rust); mutable state only in one region per phase, rendered as one
   `&mut State`. The front end is written so already: `@t` the
   checker's, `@k` the compiler's.
2. **Errors.** Control restricted to the one abort-to-error pattern,
   which becomes `Result`.
3. **Annotations.** Which Rust choices are said in types or comments:
   `Box`, `Rc` or an index; `Vec` or a list; `&` or `&mut`.
4. **What the front end uses.** If it already stays within a small
   subset, the kernel can be defined as that subset: an inventory of each
   construct's use across the front end's files, with each one's Rust
   mapping and what does not map, is the first piece of work.
