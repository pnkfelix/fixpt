; Rejected: `map` of three is three, not two.
(define map (poly ((t type) (u type) (n size)) (subr pure ((subr pure (t) u) (vec t n)) (vec u n)))
  (lambda (f xs) (if (null? xs) nil (cons (f (car xs)) (map f (cdr xs))))))
(define three (vec int 3) (cons 1 (cons 2 (cons 3 nil))))
(define doubled (vec int 2) (map (lambda ((x int)) (+ x x)) three))
