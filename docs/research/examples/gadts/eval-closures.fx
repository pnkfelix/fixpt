;;; FX-26 today: a typed evaluator with no tags at all. An `(exp a)` is
;;; its own meaning, a thunk giving an `a`, so `eval` is a call and cannot
;;; go wrong. The price: an expression can only be evaluated, never
;;; inspected, printed or optimized (tagless-final style, with one
;;; interpreter, since FX-26 has no `type -> type` kind to abstract over).
(define-type (exp (a type)) (subr pure () a))
(define int-x (subr pure (int) (exp int)) (lambda (n) (lambda () n)))
(define bool-x (subr pure (bool) (exp bool)) (lambda (b) (lambda () b)))
(define add-x (subr pure ((exp int) (exp int)) (exp int))
  (lambda (x y) (lambda () (+ (x) (y)))))
(define if-x (poly ((a type)) (subr pure ((exp bool) (exp a) (exp a)) (exp a)))
  (lambda (c t f) (lambda () (if (c) (t) (f)))))
(define eval (poly ((a type)) (subr pure ((exp a)) a)) (lambda (e) (e)))
(eval (if-x (bool-x #t) (add-x (int-x 1) (int-x 2)) (int-x 0)))
