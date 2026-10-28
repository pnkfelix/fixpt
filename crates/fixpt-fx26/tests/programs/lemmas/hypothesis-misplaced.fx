; Rejected: each field is coerced from the other one, which type-checks but
; is not the identity.
(define-generative (two (a type)) (tupof (x a) (y a)))
(define bad (proves (poly ((a type) (b type)) (<= (two a) (two b)) (<= a b)))
  (lambda (f p)
    (up-two (tup (x (f (extract (down-two p) y)))
                     (y (f (extract (down-two p) x)))))))
