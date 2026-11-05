;; => 2
;; A product of two unions below the union of its four products: split at
;; one field, then each piece at the other.
(define-type ib (oneof int bool))
(define-type four (anyof (productof (1 int) (2 int)) (productof (1 int) (2 bool))
                         (productof (1 bool) (2 int)) (productof (1 bool) (2 bool))))
(define p (productof (1 ib) (2 ib)) (product (1 #t) (2 2)))
(define q four p)
(extract p 2)
