;; ! `stage` is given a bound of `e`, which may be of less than `e` is: `e` may stand only where less is safe, in the effect, and in what is given, not taken; or give its exact evidence
;; A bound where its variable is taken: refused as the program is checked.
(define api (module (define x 41)))
(define taking
  (poly ((e effect)) (subr (maxeff stage spin e (read (globals api))) ((effectbound e) datum) int))
  (plambda ((e effect))
    (lambda (eb code)
      (stage api pure (subr e ((subr e () unit)) int) code (p 1) (why -1) (given eb)))))
0
