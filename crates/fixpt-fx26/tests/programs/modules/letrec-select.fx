;; => 3
;; A `letrec`'s types may name a module's types.
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(with counter
  (letrec ((up3 (subr pure ((select counter t)) (select counter t))
                (lambda (c) (inc (inc (inc c))))))
    (value (up3 zero))))
