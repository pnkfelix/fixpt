;; => -2
;; `attempt-within`: a body that would run for ever is cancelled once its
;; budget is spent, as the scheduler sees at a time slice's end, and the
;; on-timeout's value is the form's; the program goes on.
(define* forever (subr spin (int) int) (lambda (n) (forever (+ n 1))))
(attempt-within 1 (forever 0) (lambda ((m string)) -1) (lambda () -2))
