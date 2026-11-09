;; => 7
;; Comparing `poly`s with bounded effect binders (TODO.md §226): one with
;; none takes any effect, so it is below one with a bound; and under that
;; bound its latent `(maxeff e (read r))` is within `(read r)`.
(define any (poly ((r region) (e effect))
              (subr (maxeff e (read r)) ((subr e () int)) int))
  (plambda ((r region) (e effect)) (lambda (h) (h))))
(define tight (poly ((r region) (e effect (within (read r))))
                (subr (read r) ((subr e () int)) int))
  any)
((proj tight @c pure) (lambda () 7))
