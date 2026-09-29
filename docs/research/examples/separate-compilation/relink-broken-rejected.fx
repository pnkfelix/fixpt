;;; Rejected: a new implementation at another type makes a new global, and
;;; the client, checked again against it, fails; it is broken until defined
;;; again (the other half of section 2.4).

;;; ---- counter.fx, version 1 ----
(define step (subr pure (int) int) (lambda (n) (+ n 1)))

;;; ---- client.fx, checked against version 1 ----
(define* twice (subr pure (int) int) (lambda (n) (step (step n))))

;;; ---- counter.fx, version 2: the type changed ----
(define step (subr pure (string) int) (lambda (s) (string-length s)))
(twice 0)                                 ; error: `twice` is broken
