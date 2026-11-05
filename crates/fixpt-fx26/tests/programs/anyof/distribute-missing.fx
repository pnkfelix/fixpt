;; ! is expected here, and this is a (productof (1 ib) (2 ib))
;; Three of the four products: the piece of two `bool`s is in none.
(define-type ib (oneof int bool))
(define-type three (anyof (productof (1 int) (2 int)) (productof (1 int) (2 bool))
                          (productof (1 bool) (2 int))))
(define p (productof (1 ib) (2 ib)) (product (1 #t) (2 #t)))
(define q three p)
