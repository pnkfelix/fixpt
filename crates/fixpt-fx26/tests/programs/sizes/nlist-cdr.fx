; Rejected: the tail of three is two.
;; cons-chain: an (nlist int n): list gives no size
(define three (nlist int 3) (cons 1 (cons 2 (cons 3 nil))))
(define wrong (nlist int 3) (cdr three))
