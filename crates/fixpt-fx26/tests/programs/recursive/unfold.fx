; Two unfoldings of one recursive type are equal.
(define-type s1 (subr pure () (productof (hd int) (tl s1))))
(define-type s2 (subr pure () (productof (hd int) (tl (subr pure () (productof (hd int) (tl s2)))))))
(define f (subr pure (s2) int) (lambda (x) 0))
(define g (subr pure (s1) int) (lambda (x) (f x)))
