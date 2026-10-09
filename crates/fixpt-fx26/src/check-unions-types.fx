;;; The types of `check-unions.fx`, its `check-unions-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-ids (select check-types-types k-ids))
(define-type k-pending (productof (1 int) (2 int) (3 int)))
(define-type k-sides (pairof k-ids k-ids @t))
;; Type `t` where a value of it is found of shape `k`, and where not, -1
;; for no narrowing: a union's members of that shape, and the rest; a pair
;; that may be `nil`, the pair that is not, where `null?` does not hold or
;; `pair?` does. Nothing else is narrowed (a list found `nil` stays a list,
;; which is what `cons` onto it wants).
(define-type k-split (productof (1 int) (2 int)))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-rules.fx`).
(define-type check-unions-sig
  (moduleof (val k-false-expected?
                 (subr (maxeff (read @globals) (read @t) spin) (int) bool))))
