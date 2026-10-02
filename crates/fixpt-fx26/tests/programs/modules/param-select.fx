;; => 2
;; A parameter's type may name a module in scope.
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define* bump (subr pure ((select counter t)) (select counter t))
  (lambda ((c (select counter t))) (with counter (inc c))))
(with counter (value (bump (inc zero))))
