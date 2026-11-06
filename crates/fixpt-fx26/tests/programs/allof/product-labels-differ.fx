;; ! its members are products of the same labels, in order
(define-type bad (allof (productof (f (subr pure (int) int)) (n int))
                        (productof (n int) (f (subr pure (string) string)))))
1
