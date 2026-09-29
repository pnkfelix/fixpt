; `(mu t T)` writes a recursive type with no name; a `define-type`'s name is
; transparent, so a named type and its `mu` are each a subtype of the other.
; Recursive types with no name print as `(mu %d …)`, which reads back.
(define-type ilist (sumof (nil unit) (cell (productof (hd int) (tl ilist)))))
(define f (subr pure ((mu t (sumof (nil unit) (cell (productof (hd int) (tl t)))))) int)
  (lambda (x) 0))
(define* g (subr pure (ilist) int) (lambda (x) (f x)))
(define* h (subr pure ((mu t (sumof (nil unit) (cell (productof (hd int) (tl t)))))) int)
  (lambda (x) (g x)))
(define k (subr pure ((mu %2 (subr pure (%2) int))) int) (lambda (x) 1))
