;;; The same, every procedure reading any global: the redefinition of `g`
;;; refused, as one that may reach itself.
(define-type box (productof (p (poly ((e effect)) (subr e ((subr e () int)) int)))))
(define tbl box (product (p (plambda ((e effect)) (lambda (k) (k))))))
(define g (subr (read @globals) () int) (lambda () 0))
(define f (subr (read @globals) () int)
  (let ((h g)) (lambda () ((proj (extract tbl p) (read @globals)) h))))
(define g (subr (read @globals) () int) (lambda () (f)))
