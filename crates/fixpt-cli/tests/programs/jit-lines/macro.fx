(define-syntax twice (expr) (syntax-rules () ((_ e)
  (let ((v e)) (+ v (+ v (* v 0)))))))
;; `f`'s code from the template above, placed at its use below.
(define* f (subr pure (int) int)
  (lambda (x)
    (twice (* x 3))))
(f 2)
