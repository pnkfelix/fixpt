;;; `map` keeps a length: in the `else` of `(null? xs)` the checker knows
;;; `n ≥ 1`, so the tail of `xs` is `n - 1` long, and so is the result of the
;;; recursive call; and it works on a `nlist` of some length too.
(define-type map-type
  (poly ((t type) (u type) (n size)) (subr pure ((subr pure (t) u) (nlist t n)) (nlist u n))))
(define map map-type
  (plambda ((t type) (u type) (n size))
    (proj (letrec ((map map-type
                    (lambda (f xs) (if (null? xs) nil (cons (f (car xs)) (map f (cdr xs)))))))
            map)
          t u n)))
;; cons-chain: an (nlist int n): list gives no size
(define three (nlist int 3) (cons 1 (cons 2 (cons 3 nil))))
(define doubled (nlist int 3) (map (lambda ((x int)) (+ x x)) three))
(define some (nlist int finite) (map (lambda ((x int)) x) (the (nlist int finite) three)))
