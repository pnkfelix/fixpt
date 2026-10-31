;; ! `stage`'s code is checked, as the program runs, against `e`, a variable: give it its evidence, a `(effectrep e)` (`reify-effect`), in `(given …)`
;; Evidence missing: refused as the program is checked.
(define api (module (define x 41)))
(define within
  (poly ((e effect)) (subr (maxeff stage spin e (read (globals api))) (datum) int))
  (plambda ((e effect))
    (lambda (code) (stage api e int code (p (p)) (why -1)))))
((proj within pure) '(+ x 1))
