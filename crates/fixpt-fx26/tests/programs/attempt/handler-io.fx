;; => 0
;; On-failure runs after, outside the body, and may do I/O.
(define* report (subr (io stderr) (string) int)
  (lambda (m) (begin (write-err "") 0)))
(attempt (quotient 1 0) report)
