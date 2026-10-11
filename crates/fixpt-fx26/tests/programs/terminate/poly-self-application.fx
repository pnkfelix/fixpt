; Rejected: `app` calls its `f` on its `x`; at `T`, a procedure type taking a
; `T`, `((proj app T) w w)` gives `w` itself, looping with no `spin` in sight
; (docs/research/soundness-findings.md, F17).
(define-type T (subr pure (T) int))
(define omega (subr pure () int)
  (lambda ()
    (let ((app (the (poly ((t type)) (subr pure ((subr pure (t) int) t) int))
                    (plambda ((t type)) (lambda ((f (subr pure (t) int)) (x t)) (f x))))))
      (let ((w (the T (lambda (x) ((proj app T) x x)))))
        ((proj app T) w w)))))
