;; ! is expected here
;; An abstract type where a transparent one is wanted: refused.
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define-type known
  (moduleof (desc t int) (val zero t) (val inc (subr pure (t) t)) (val value (subr pure (t) int))))
(the known counter)
