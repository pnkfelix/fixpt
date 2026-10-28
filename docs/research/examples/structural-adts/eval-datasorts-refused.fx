;;; Refused: `1 + #t` is an `any-exp`, but no `int-exp`.
(define-type int-exp
  (oneof (int-e int)
         (add (tupof (l int-exp) (r int-exp)))
         (if-e (tupof (c bool-exp) (t int-exp) (f int-exp)))))
(define-type bool-exp
  (oneof (bool-e bool)
         (is-zero int-exp)
         (if-e (tupof (c bool-exp) (t bool-exp) (f bool-exp)))))
(define bad int-exp (one add (tup (l (one int-e 1)) (r (one bool-e #t)))))
