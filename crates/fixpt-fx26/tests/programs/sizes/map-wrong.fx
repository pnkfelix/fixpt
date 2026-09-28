; Rejected: `map` of three is three, not two.
(define map (poly ((t type) (u type) (n size)) (subr pure ((subr pure (t) u) (nlist t n)) (nlist u n)))
  (plambda ((t type) (u type) (n size))
    (proj (letrec ((map (poly ((t type) (u type) (n size)) (subr pure ((subr pure (t) u) (nlist t n)) (nlist u n)))
                    (lambda (f xs) (if (null? xs) nil (cons (f (car xs)) (map f (cdr xs)))))))
            map)
          t u n)))
(define three (nlist int 3) (cons 1 (cons 2 (cons 3 nil))))
(define doubled (nlist int 2) (map (lambda ((x int)) (+ x x)) three))
