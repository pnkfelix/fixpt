;; ! beyond what is expected, it has spin
;; A procedure that may be given itself through a description function's
;; application: calling it may not end, so its caller must say `spin`.
(define-type (selfy (f (=> type type))) (subr pure ((f (selfy f))) int))
(define go (poly ((f (=> type type))) (subr pure ((selfy f) (f (selfy f))) int))
  (plambda ((f (=> type type))) (lambda (s x) (s x))))
