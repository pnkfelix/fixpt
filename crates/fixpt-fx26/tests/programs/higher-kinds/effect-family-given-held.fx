;; ! beyond what is expected, it has (io stdout)
;; The effect an effect family gives, given where an effect is wanted, is
;; held to: a thunk that writes out is not within `(rw @h)`.
(define-type rw (dlambda ((r region)) (maxeff (read r) (write r))))
(define run (poly ((e effect)) (subr e ((subr e () int)) int))
  (plambda ((e effect)) (lambda (f) (f))))
((proj run (rw @h)) (lambda () (begin (write-out "x") 1)))
