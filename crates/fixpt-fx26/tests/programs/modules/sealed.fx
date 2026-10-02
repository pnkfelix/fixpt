;; ! unbound variable `inc`
;; Sealed by `the`: what its type leaves out is gone.
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define sealed (the (moduleof (abs t type) (val zero t) (val value (subr pure (t) int))) counter))
(with sealed (inc zero))
