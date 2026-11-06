;; ! an `allof`'s members differ at `n`, a int and a string: only procedures, and products of them, may
;; Where products differ in a field that holds no procedure, they have no
;; meet written: one value cannot be both.
(define-type bad (allof (productof (f (subr pure (int) int)) (n int))
                        (productof (f (subr pure (string) string)) (n string))))
1
