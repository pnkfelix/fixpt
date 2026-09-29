;;; A size binder that sizes only one argument may be `finite`: the one
;;; list supplies it, and the result only forgets it.
(define copy (poly ((n size)) (subr pure ((nlist int n)) (nlist int n)))
  (plambda ((n size))
    (proj (letrec ((copy (poly ((n size)) (subr pure ((nlist int n)) (nlist int n)))
                    (plambda ((n size))
                      (lambda (xs) (if (null? xs) nil (cons (car xs) (copy (cdr xs))))))))
            copy)
          n)))
(define some (nlist int finite) (list 1 2))
(length (copy some))
