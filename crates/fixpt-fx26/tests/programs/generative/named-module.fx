;;; A module's generative type, its conversions named: inside, they cross;
;;; outside, the type is abstract and only what the module makes of them.
(define m
  (module
    (define-generative t int #:seal mk #:unseal get)
    (define zero t (mk 0))
    (define inc (subr pure (t) t) (lambda (c) (mk (+ (get c) 1))))
    (define value (subr pure (t) int) (lambda (c) (get c)))))
(with m (value (inc (inc zero))))
