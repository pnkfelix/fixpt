;;; FX-26 today: a structural family may mention itself at other,
;;; fixed descriptions, `(expr bool)` inside `(expr a)`, since its
;;; instances stay finitely many. The branch condition must be an
;;; `(expr bool)`, and a literal `0` there is refused.
(define-type (expr (a type))
  (oneof (lit a) (if-e (tupof (c (expr bool)) (t (expr a)) (f (expr a))))))
(define* ev (poly ((a type)) (subr spin ((expr a)) a))
  (lambda (e)
    (tagcase e
      (lit x x)
      (if-e (c t f) (if (ev c) (ev t) (ev f))))))
(define e1 (expr int) (one if-e (tup (c (one lit #t)) (t (one lit 1)) (f (one lit 2)))))
(ev e1)
