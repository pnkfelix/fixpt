(define-type pt (productof (x int) (y int)))
(define scale int 10)
(define mk (subr pure (int int) pt) (lambda (x y) (product (x x) (y y))))
