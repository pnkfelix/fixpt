;;; The types of `check-infer.fx`, its `check-infer-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-binders (select check-types-types k-binders))
(define-type k-map (select check-types-types k-map))
(define-type k-solved (ref k-map @t))
;; Binders, and the type under them.
(define-type k-bound-body (productof (1 k-binders) (2 int)))
;; A count of such occurrences, and of parameters sized by `v` alone.
(define-type k-counts (productof (1 int) (2 int)))
