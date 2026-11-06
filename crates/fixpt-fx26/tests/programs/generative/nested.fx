;;; A non-regular representation, fine since a generative name is never
;;; expanded: `nest` mentions `(nest (productof …))` in itself.
(define-type (pair (a type)) (tupleof a a))
(define-generative (nest (a type))
  (sumof (none unit) (more (tupleof a (nest (pair a))))))
(define n (nest int) (up-nest (sum more (tuple 1 (up-nest (sum none #u))))))
(define-rec (size (subr (read @globals) ((nest int)) int)
              (lambda (x) (tagcase (down-nest x) (none u 0) (more (h t) 1)))))
(size n)
