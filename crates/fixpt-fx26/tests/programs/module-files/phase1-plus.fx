;; A phase-1 form's helper (`procedural/for-syntax-load.fx`), which loads a
;; file of its own directory.
(define b (load-module "phase1-base.fx"))
(define plus-base (subr pure (int) int) (lambda (n) (+ n (with b base))))
