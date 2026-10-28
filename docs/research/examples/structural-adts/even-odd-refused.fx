;;; Refused: an odd list where an even one is expected.
(define-type even (oneof (nil unit) (cons (tupof (hd int) (tl odd)))))
(define-type odd  (oneof (cons (tupof (hd int) (tl even)))))
(define o1 odd (one cons (tup (hd 7) (tl (one nil #u)))))
(define bad even o1)
