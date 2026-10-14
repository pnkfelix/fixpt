;; ! every branch failed
;; A `race` whose branches all fail fails, as the last of them did.
(define* lost (subr pure () int) (lambda () (error "every branch failed")))
(define* fails (subr spin (int) int) (lambda (n) (if (= n 0) (lost) (fails (- n 1)))))
(race (fails 3) (fails 5))
