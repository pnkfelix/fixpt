;; => 0
;; A type of the structure of a module's description is printed by its
;; `select`, `f`'s parameter as `(select m pt)`; a module's own description
;; is not, which would name it by itself (`n`'s `pt`).
(define m
  (module (define-type pt (productof (x int) (y int))) (define origin pt (product (x 0) (y 0)))))
(define f (subr pure ((productof (x int) (y int))) int) (lambda (p) (extract p x)))
(define n (module (import m (type pt)) (define g (subr pure (pt) pt) (lambda (p) p))))
0
