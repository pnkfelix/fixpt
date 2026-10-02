;; => 1
;; The same values in another order.
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define-type reordered
  (moduleof (abs t type) (val value (subr pure (t) int)) (val inc (subr pure (t) t)) (val zero t)))
(define one (subr pure (reordered) int) (lambda (m) (with m (value (inc zero)))))
(one counter)
