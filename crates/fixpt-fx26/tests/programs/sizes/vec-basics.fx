;;; A `vec` built by `cons`, taken apart by `cdr`, walked with no `spin`,
;;; and seen as a finite list and back.
(define three (vec int 3) (cons 1 (cons 2 (cons 3 nil))))
(define len (subr pure ((vec int finite) int) int) (lambda (xs n) (if (null? xs) n (len (cdr xs) (+ n 1)))))
(define two (vec int 2) (cdr three))
(define as-list (listof int finite) three)
(define back (vec int finite) as-list)
(+ (len three 0) (car two))
