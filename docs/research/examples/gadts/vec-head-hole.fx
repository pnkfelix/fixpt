;;; A hole found writing these examples (2026-09-29): accepted by both
;;; checkers, and fails at run time ("expected a pair: ()"). Inference does
;;; not solve `n + 1 = 0`, leaves `n` as `finite`, and `(+ finite 1)` is
;;; `finite`, which an `(nlist int 0)` fits. The F4 rule of
;;; soundness-findings.md refuses `finite` for a size that is "of something
;;; inside" an argument when the argument is itself `finite`, but not here.
;;; It should be refused, as `vec-head-refused.fx` is.
(define head (poly ((t type) (n size)) (subr pure ((nlist t (+ n 1))) t))
  (lambda (xs) (car xs)))
(head (the (nlist int 0) nil))
