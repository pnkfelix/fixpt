;; => 1002
;; Attempts nest: an inner one's failure is its own, and an outer body
;; that fails after an inner one caught a failure is the outer's.
(define* inner (subr nondet (int) int)
  (lambda (n) (attempt (quotient 100 n) (lambda ((m string)) 1000))))
(define* outer (subr nondet (int) int)
  (lambda (n) (attempt (+ (inner n) (quotient 1 (- n 1))) (lambda ((m string)) 2))))
(+ (outer 0) (+ (outer 1) (outer 100)))
