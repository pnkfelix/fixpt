;; => 1
;; A module given to a procedure that takes one of its type.
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
;; Its type named, as any type may be.
(define-type counters
  (moduleof (abs t type) (val zero t) (val inc (subr pure (t) t)) (val value (subr pure (t) int))))
(define use (subr pure (counters) int)
  (lambda (m) (with m (value (inc zero)))))
(use counter)
