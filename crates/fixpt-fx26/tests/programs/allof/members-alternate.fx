;; ! it counts up, but nothing fixed bounds the count above
;; Each member's own calls go to the other: under `symbol`, to the `int`
;; member with `n` less by one; under `int`, back with `n` more by one. The
;; loop through both grows `n`, so neither member ends, though the calls
;; under one alone would.
(define f (allof (subr pure (symbol nat) int) (subr pure (int nat) int))
  (letrec ((f (allof (subr pure (symbol nat) int) (subr pure (int nat) int))
             (lambda (x n)
               (cond ((symbol? x) (if (= n 0) 0 (f 1 (- n 1))))
                     (else (f (quote a) (+ n 1)))))))
    f))
(f (quote a) 3)
