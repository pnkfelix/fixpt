;; => 1
;; `error`'s message, as given, is what on-failure is called with.
(define* work (subr spin (int) string) (lambda (k) (if (= k 0) (error "bad input") "fine")))
(attempt (if (string=? (work 0) "fine") 2 3)
         (lambda ((m string)) (if (string=? m "bad input") 1 0)))
