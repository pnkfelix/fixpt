;; => 2
;; A procedure that constructs is written as one, the keyword at the head:
;; a keyword is no procedure.
(define ok (subr pure (int) (sumof (#:ok int))) (lambda (x) (#:ok x)))
(tagcase (ok 2) (#:ok n n))
