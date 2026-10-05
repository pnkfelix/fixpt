;; ! `x` is defined twice in this module
;; A module defining a name twice has no type: `(moduleof (val x int) (val x
;; string))` is refused, and until this was it checked, and a function
;; taking `(moduleof (val x int))` got 42 natively but "expected an exact
;; integer" lowered, one path using the first `x` and the other the last
;; (PLAN.md Q13, O16).
(define m (module (define x int 1) (define x string "s")))
(define f (subr pure ((n (moduleof (val x int)))) int) (lambda (n) (with n (+ x 41))))
(f m)
