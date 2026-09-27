; Rejected: a family that is only itself names no type.
(define-type (loop (t type)) (loop t))
(define x (loop int) 1)
