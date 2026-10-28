;;; A non-regular representation, fine since a generative name is never
;;; expanded: `nest` mentions `(nest (tupof …))` in itself.
(define-type (pair (a type)) (tupof (l a) (r a)))
(define-generative (nest (a type))
  (oneof (none unit) (more (tupof (hd a) (tl (nest (pair a)))))))
(define n (nest int) (up-nest (one more (tup (hd 1) (tl (up-nest (one none #u)))))))
(define-rec (size (subr (read @globals) ((nest int)) int)
              (lambda (x) (tagcase (down-nest x) (none u 0) (more (h t) 1)))))
(size n)
