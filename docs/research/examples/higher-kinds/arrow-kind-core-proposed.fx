;; PROPOSED — Path 1 (arrow kinds in the core). None of this parses
;; today; `parse_kind` only accepts the seven base kinds
;; (`crates/fixpt-fx26/src/parse.rs:98-109`), and there is no `Ty`
;; variant for "a type variable applied to arguments" at all
;; (`crates/fixpt-fx26/src/ast.rs`, `enum Ty`). Confirmed by running
;; `target/release/fixpt check` on this file (2026-10-02): both
;; checkers reject it at the first new form, line 14 col 30 (the
;; `(=> type type)` kind), with "a kind is `region`, `place`, `effect`,
;; `type`, `data`, `size` or `conv`".
;;
;; A binder of kind `(=> type type)`: `f` ranges over one-argument type
;; constructors (`listof` partially applied to its region, `box`, …),
;; and `(f a)` is type-level application.
(define-type (functor-sig (f (=> type type)))
  (moduleof (abs dummy type)                    ; PROPOSED shape only
            (val fmap (poly ((a type) (b type))
                        (subr pure ((subr pure (a) b) (f a)) (f b))))))

;; An explicit-head use: `f` is supplied by the CALLER, never guessed by
;; the checker. This is the tractable case (Jones 1995 §3.5; Xie,
;; Eisenberg & Oliveira POPL 2020): the pattern `(f a)` has a rigid,
;; already-known head, so matching it against an actual argument type is
;; ordinary first-order congruence, exactly like `Ty::Named`'s existing
;; `(which, args)` comparison (`check.rs:2006-2025`) extended to a bound
;; variable head instead of a fixed `which: u32`.
(define map-list
  (poly ((a type) (b type))
    (subr pure ((subr pure (a) b) (listof a acyclic)) (listof b acyclic)))
  (plambda ((a type) (b type))
    (lambda (f xs) (if (null? xs) nil (cons (f (car xs)) (map-list f (cdr xs)))))))

;; The HARD case this note's Path 1 section argues against ever
;; allowing: solving for an UNKNOWN `f` from an equation between an
;; application and a concrete type.
;;
;;   (proj generic-call (?f) (the (listof int acyclic) ...))
;;   ;; requires solving   (?f int) =?= (listof int acyclic)
;;   ;; for ?f — higher-order unification, undecidable outside the
;;   ;; Miller-pattern fragment (Miller, JLC 1991), and GHC's kind
;;   ;; inference deliberately never attempts it (Xie, Eisenberg &
;;   ;; Oliveira, POPL 2020, §1: "the type language does not include
;;   ;; lambdas").
;;
;; Path 1's recommendation (see the note) is to never let `proj`
;; reconstruct a binder of arrow kind: such a binder must always be
;; supplied explicitly, as `map-list` above supplies none at all because
;; its only type-constructor use (`listof`) is a built-in, not a
;; variable.
