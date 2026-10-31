;; ! `reify-effect` makes exact evidence, so it is given exact evidence, and this is a bound of `e`
;; Exact evidence made of a bound: refused as the program is checked.
(define more
  (poly ((e effect)) (subr pure ((effectbound e)) (effectrep (maxeff e (io stdout)))))
  (plambda ((e effect)) (lambda (eb) (reify-effect (maxeff e (io stdout)) (given eb)))))
0
