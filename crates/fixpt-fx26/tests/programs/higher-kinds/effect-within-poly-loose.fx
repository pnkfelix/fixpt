;; ! beyond what is expected, it has e
;; With no bound, `e` is not within `(read r)` (TODO.md §226).
(define any (poly ((r region) (e effect))
              (subr (maxeff e (read r)) ((subr e () int)) int))
  (plambda ((r region) (e effect)) (lambda (h) (h))))
(define loose (poly ((r region) (e effect))
                (subr (read r) ((subr e () int)) int))
  any)
