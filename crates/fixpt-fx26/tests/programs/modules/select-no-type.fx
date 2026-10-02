;; ! `(select counter u)`: `counter` has no type `u`
;; `select` names one of the module's types; values are not types.
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define z (select counter u) (with counter zero))
