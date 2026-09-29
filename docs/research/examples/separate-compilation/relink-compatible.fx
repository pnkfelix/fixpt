;;; Linking as redefinition, in FX-26 today at one-file grain: a new
;;; implementation at the same type is taken by the client already checked,
;;; with no re-check (the cutoff of section 2.4).

;;; ---- counter.fx, version 1 ----
(define step (subr pure (int) int) (lambda (n) (+ n 1)))

;;; ---- client.fx, checked against version 1 ----
(define* twice (subr pure (int) int) (lambda (n) (step (step n))))
(twice 0)                                 ; 2

;;; ---- counter.fx, version 2: same type, new body ----
(define step (subr pure (int) int) (lambda (n) (+ n 10)))
(twice 0)                                 ; 20: the client sees version 2
