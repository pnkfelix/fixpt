; Arguments that together instantiate one type binder join as branches do
; (`docs/fx26.md`, "Products and sums"): `list`'s elements of different
; sums make a list of their join, a variable's sum too.
(define x (sum #:b "x"))
(define xs (list (sum #:a 1) x (sum #:c #t) (sum #:a 2)))
(define score (subr pure ((sumof (#:a int) (#:b string) (#:c bool))) int)
  (lambda (s) (tagcase s (#:a n n) (#:b t 10) (#:c b 100))))
(define total (->* ((listof (sumof (#:a int) (#:b string) (#:c bool)) acyclic)) int)
  (lambda (l) (if (null? l) 0 (+ (score (car l)) (total (cdr l))))))
(total xs)
