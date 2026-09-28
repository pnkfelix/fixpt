; Frozen lists are covariant: a list of a smaller sum fits a list of a
; larger one.
(define-type n1 (sumof (a int)))
(define-type n2 (sumof (a int) (b int)))
(define f (subr pure ((listof n2 const)) int) (lambda (x) 0))
(define* g (subr pure ((listof n1 const)) int) (lambda (x) (f x)))
