; Rejected: one more than two is three, not four.
(define xs (nlist int 2) (cons 1 (cons 2 nil)))
(define ys (nlist int 3) (cons 0 xs))
(define zs (nlist int 4) (cons 0 xs))
