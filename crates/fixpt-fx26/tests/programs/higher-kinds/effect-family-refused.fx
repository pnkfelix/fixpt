;; ! beyond what is expected, it has (e r)
;; Calling a procedure whose effect is `(e r)`, for an unknown effect
;; family `e`, has that effect, which a pure procedure may not have.
(define bad (poly ((e (=> (region) effect)) (r region)) (subr pure ((subr (e r) () int)) int))
  (plambda ((e (=> (region) effect)) (r region)) (lambda (f) (f))))
