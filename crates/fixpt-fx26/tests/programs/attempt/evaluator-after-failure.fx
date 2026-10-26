;; => 1000
;; On `fx-ast-eval`, a poll in the few applications between a failure and
;; the scheduler taking it found no prompt to suspend to, when a tick fell
;; there ("no prompt for this tag"): the earlier form and the count put one
;; there. A failed task is quiet now until taken (`TASK_FAILED`; Heist's,
;; `FIXPT-CHANGES.md` F2).
(+ 1 2)
(define* step (subr nondet (int) int)
  (lambda (i) (attempt (quotient 2 (remainder i 2)) (lambda ((m string)) 0))))
(define* loop (subr (maxeff nondet spin) (int int) int)
  (lambda (i acc) (if (= i 0) acc (loop (- i 1) (+ acc (quotient (step i) 2))))))
(loop 2000 0)
