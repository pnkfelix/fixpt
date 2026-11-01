;; => 8
;; `attempt-within` twice: a body cancelled at its budget leaves nothing
;; behind, and the next one runs, and ends, as if the first had not been.
(define* forever (subr spin (int) int) (lambda (n) (forever (+ n 1))))
(define* twice (subr spin (int) int) (lambda (n) (* 2 n)))
(+ (attempt-within 1 (forever 0) (lambda ((m string)) 0) (lambda () 2))
   (attempt-within 10000 (twice 3) (lambda ((m string)) 0) (lambda () 100)))
