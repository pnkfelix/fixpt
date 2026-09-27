; Rejected: one more than two is three, not four.
(define xs (vec int 2) (cons 1 (cons 2 nil)))
(define ys (vec int 3) (cons 0 xs))
(define zs (vec int 4) (cons 0 xs))
