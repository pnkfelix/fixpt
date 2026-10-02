;; => 3
;; `(select m t)` names the abstract type, in annotations.
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define two (select counter t) (with counter (inc (inc zero))))
(with counter (value (inc (the (select counter t) two))))
