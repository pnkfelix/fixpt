;; ! its members are products of the same labels, in order
;; Products are not mixed with procedure types.
(define-type bad (allof (productof (f (subr pure (int) int)))
                        (subr pure (string) string)))
1
