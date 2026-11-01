;;; A knot through a kept procedure's effect variable: `f` keeps the first
;;; `g` and passes it to what `tbl` holds, at `g`'s effect; `g` is defined
;;; again to call `f`. Instantiating the variable carries `g`'s reads into
;;; `f`'s, so `f` reads `f`: refused.
(define-type box (productof (p (poly ((e effect)) (subr e ((subr e () int)) int)))))
(define tbl box (product (p (plambda ((e effect)) (lambda (k) (k))))))
(define g (subr (read (globals tbl f)) () int) (lambda () 0))
(define f (subr (read (globals tbl f)) () int)
  (let ((h g)) (lambda () ((proj (extract tbl p) (read (globals tbl f))) h))))
(define g (subr (read (globals tbl f)) () int) (lambda () (f)))
