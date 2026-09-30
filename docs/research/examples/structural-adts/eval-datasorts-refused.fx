;;; Refused: `1 + #t` is an `any-exp`, but no `int-exp`.
(define-type int-exp
  (sumof (int-e int)
         (add (productof (l int-exp) (r int-exp)))
         (if-e (productof (c bool-exp) (t int-exp) (f int-exp)))))
(define-type bool-exp
  (sumof (bool-e bool)
         (is-zero int-exp)
         (if-e (productof (c bool-exp) (t bool-exp) (f bool-exp)))))
(define bad int-exp (sum add (product (l (sum int-e 1)) (r (sum bool-e #t)))))
