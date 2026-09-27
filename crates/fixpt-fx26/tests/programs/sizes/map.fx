;;; `map` keeps a length: in the `else` of `(null? xs)` the checker knows
;;; `n ≥ 1`, so the tail of `xs` is `n - 1` long, and so is the result of the
;;; recursive call; and it works on a `vec` of some length too.
(define map (poly ((t type) (u type) (n size)) (subr pure ((subr pure (t) u) (vec t n)) (vec u n)))
  (lambda (f xs) (if (null? xs) nil (cons (f (car xs)) (map f (cdr xs))))))
(define three (vec int 3) (cons 1 (cons 2 (cons 3 nil))))
(define doubled (vec int 3) (map (lambda ((x int)) (+ x x)) three))
(define some (vec int finite) (map (lambda ((x int)) x) (the (vec int finite) three)))
