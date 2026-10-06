;; => 5
;; A `define*` that calls itself: while first checked it is at its type as
;; written, so its calls of itself read nothing more (`count` reads `step`).
(define step int 1)
(define m (module
  (define* count (subr spin (int) int) (lambda (n) (if (< n 1) 0 (+ step (count (- n step))))))))
(with m (count 5))
