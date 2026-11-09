;; => 13
;; Bounded binders found from the arguments, then checked against their
;; bounds (TODO.md §226): `r` from the reference, `e` from the handler.
(define run (poly ((r region) (e effect (within (read r))))
              (subr (read r) ((ref int r) (subr e () int)) int))
  (plambda ((r region) (e effect (within (read r)))) (lambda (c h) (+ (get c) (h)))))
(let ((c (the (ref int @c) (new 3))))
  (+ (run c (lambda () (get c))) (run c (lambda () 4))))
