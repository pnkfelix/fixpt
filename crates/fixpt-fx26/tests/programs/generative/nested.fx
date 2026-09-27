;;; A non-regular representation, fine since a generative name is never
;;; expanded: `nest` mentions `(nest (productof …))` in itself.
(define-generative (nest (a type)) (sumof (none unit) (more (productof (hd a) (tl (nest (productof (l a) (r a))))))))
(define n (nest int) (up-nest (sum more (product (hd 1) (tl (up-nest (sum none #u)))))))
(define-rec (size (subr pure ((nest int)) int) (lambda (x) (tagcase (down-nest x) (none u 0) (more (h t) 1)))))
(size n)
