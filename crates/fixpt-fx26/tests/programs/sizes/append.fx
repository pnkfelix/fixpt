;;; `append` adds lengths; sizes are naturals, so `n + m - 1 ≥ 0` follows
;;; from `n - 1 ≥ 0`.
(define app (poly ((t type) (n size) (m size)) (subr pure ((nlist t n) (nlist t m)) (nlist t (+ n m))))
  (plambda ((t type) (n size) (m size))
    (proj (letrec ((app (poly ((t type) (n size) (m size)) (subr pure ((nlist t n) (nlist t m)) (nlist t (+ n m))))
                    (lambda (xs ys) (if (null? xs) ys (cons (car xs) (app (cdr xs) ys))))))
            app)
          t n m)))
(define len (subr pure ((nlist int finite)) int)
  (letrec ((len (subr pure ((nlist int finite)) int)
             (lambda (xs) (if (null? xs) 0 (+ 1 (len (cdr xs)))))))
    len))
(define five (nlist int 5) (app (the (nlist int 2) (cons 1 (cons 2 nil))) (the (nlist int 3) (cons 3 (cons 4 (cons 5 nil))))))
(len five)
