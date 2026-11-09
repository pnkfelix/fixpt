;; ! `e` is bound within (maxeff (read @c) (write @c)), and (io stdout) is not: it has (io stdout)
;; An instantiation beyond the bound is refused (TODO.md §226).
(define run (poly ((r region) (e effect (within (maxeff (read r) (write r)))))
              (subr (maxeff (read r) (write r)) ((subr e () int)) int))
  (plambda ((r region) (e effect (within (maxeff (read r) (write r)))))
    (lambda (h) (+ (h) 1))))
((proj run @c (io stdout)) (lambda () (begin (write-out "x") 1)))
