;;; The types of `check-bounds.fx`, its `check-bounds-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-map (select check-types-types k-map))
(define-effect kstate (select check-types-types kstate))
;; At least `1`, at most `2`, exactly `3`: types, -1 where nothing has said.
(define-type k-bound (productof (1 int) (2 int) (3 int)))
(define-type k-bound-map (ref (listof (pairof int k-bound @t) @t) @t))
;; Each instantiation's solution so far, and its binders' bounds, innermost
;; first. An instantiation that fails leaves its entry, found by no one.
(define-type k-bound-entry (pairof (ref k-map @t) k-bound-map @t))
;; The bounds kept for `solved`, in a list of one; none if none are.
(define-type k-maybe-bounds (listof k-bound-map @t))
;; The bounds `solved` keeps for type binder `v`, if they have not met:
;; neither fixed, nor at least and at most one type (the Rust checker's
;; `unsettled`); in a list of one, or none.
(define-type k-maybe-bound (listof k-bound @t))
;; `k-unify`'s flags, set for `f`: in something invariant; matching what is
;; expected (from above); in a subroutine's parameters (the other way).
(define-type k-unifying (subr (maxeff kstate spin) () unit))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-rules.fx`).
(define-type check-bounds-sig
  (moduleof (val k-new-bounded-solved
                 (subr (maxeff (alloc @t) (read @t) (write @t)) () (ref k-map @t)))))
