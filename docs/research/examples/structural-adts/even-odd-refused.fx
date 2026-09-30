;;; Refused: an odd list where an even one is expected.
(define-type even (sumof (nil unit) (cons (productof (hd int) (tl odd)))))
(define-type odd  (sumof (cons (productof (hd int) (tl even)))))
(define o1 odd (sum cons (product (hd 7) (tl (sum nil #u)))))
(define bad even o1)
