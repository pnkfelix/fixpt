; Rejected: the tail of three is two.
(define three (vec int 3) (cons 1 (cons 2 (cons 3 nil))))
(define wrong (vec int 3) (cdr three))
