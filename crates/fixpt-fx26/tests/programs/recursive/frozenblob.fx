; Frozen bloblets are covariant too, through a recursive type.
(define-type n1 (sumof (a int)))
(define-type n2 (sumof (a int) (b int)))
(define-type b1 (bloblet (frozen n1 b1) @r))
(define-type b2 (bloblet (frozen n2 b2) @r))
(define f (subr pure (b2) int) (lambda (x) 0))
(define g (subr pure (b1) int) (lambda (x) (f x)))
