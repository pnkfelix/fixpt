;; => 4
;; Beyond FX-91: a description function to an effect. `rw` an effect
;; abbreviation (`bump`'s), and `run` polymorphic in an effect family
;; `e`, given `rw`.
(define-type rw (dlambda ((r region)) (maxeff (read r) (write r))))
(define bump (poly ((r region)) (subr (rw r) ((ref int r)) unit))
  (plambda ((r region)) (lambda (c) (set c (+ 1 (get c))))))
(define run (poly ((e (=> region effect)) (r region)) (subr (e r) ((subr (e r) () int)) int))
  (plambda ((e (=> region effect)) (r region)) (lambda (f) (f))))
(letregion r
  (let ((c (the (ref int r) (new 3))))
    ((proj run rw r) (lambda () (begin (set c (+ 1 (get c))) (get c))))))
