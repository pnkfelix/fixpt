; `(-> (param …) result)` is `(subr pure (param …) result)`: in a
; signature, as a parameter, as a result, with a named parameter and a
; test's result, and under `poly`.
(define twice (poly ((t type)) (-> ((-> (t) t) t) t))
  (lambda (f x) (f (f x))))
(define inc (-> (int) int) (lambda (x) (+ x 1)))
(define adder (-> (int) (-> (int) int)) (lambda (n) (lambda (x) (+ x n))))
(define is-int (-> ((union int string)) (bool (then (shape 0 int)) (else))) int?)
(define same (subr pure ((-> (int) int)) (subr pure (int) int)) (lambda (f) f))
(define pick (-> ((v : (union int string))) int)
  (lambda (v) (if (int? v) v 0)))
(+ (twice (same inc) 40) (+ (twice (adder 100) (pick 0)) (pick "no")))
