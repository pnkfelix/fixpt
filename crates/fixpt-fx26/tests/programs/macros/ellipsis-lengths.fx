;; ! `a` and `b`, repeated together, are given 2 and 1 times
(define-syntax zip-sum
  ((expr ...) (expr ...))
  (syntax-rules ()
    ((_ (a ...) (b ...)) (list (+ a b) ...))))
(zip-sum (1 2) (3))
