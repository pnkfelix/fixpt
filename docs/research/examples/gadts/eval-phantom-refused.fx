; Refused: with phantom-typed constructors, `1 + #f` does not check.
(define-datatype expr (int-e int) (bool-e bool) (add expr expr))
(define-generative (exp (a type)) expr)
(define* int-x (subr pure (int) (exp int)) (lambda (n) (up-exp (int-e n))))
(define* bool-x (subr pure (bool) (exp bool)) (lambda (b) (up-exp (bool-e b))))
(define* add-x (subr pure ((exp int) (exp int)) (exp int))
  (lambda (x y) (up-exp (add (down-exp x) (down-exp y)))))
(add-x (int-x 1) (bool-x #f))
