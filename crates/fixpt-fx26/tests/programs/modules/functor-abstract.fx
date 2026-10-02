;; => 2
;; A dependent procedure given a module with an abstract type: its result
;; is that module's type.
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define-type counters
  (moduleof (abs t type) (val zero t) (val inc (subr pure (t) t)) (val value (subr pure (t) int))))
(define twice (subr pure ((c counters) (select c t)) (select c t))
  (lambda (c x) (with c (inc (inc x)))))
(with counter (value (twice counter zero)))
