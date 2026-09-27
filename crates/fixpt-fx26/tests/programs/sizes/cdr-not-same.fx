; Rejected: the tail of `n` elements is `n - 1`, not `n`.
(define bad (poly ((t type) (n size)) (subr pure ((vec t n)) (vec t n)))
  (lambda (xs) (if (null? xs) nil (cdr xs))))
