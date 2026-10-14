;; ! a deadlock
;; A monitored process fails while a branch of it waits for a deadline ten
;; minutes away: the branch is cancelled, and ends at once, its timer taken
;; back, so a wait for what no task will fill is a deadlock at once, not
;; after the first task has slept until the branch's deadline.
(define-type report (sumof (ok int) (failed string)))
(define total (icell int @d) (make-icell))
(define never (icell int @e) (make-icell))
(define collector (addr report @p)
  (spawn (box report r)
    (tagcase (receive box)
      (ok v (icell-put! total v))
      (failed m (icell-put! total 100)))))
(define* failed (subr pure (string) report) (lambda (m) (sum failed m)))
(define* far (subr (maxeff (io clock)) () i64)
  (lambda () (i64+ (clock) (int->i64 600000000000))))
(define w (addr int @w)
  (spawn-monitored collector failed (box int r)
    (let ((n (receive box)))
      (par ((a (pselect ((sleep-until (far)) u 0)))
            (b (if (= n 0) (error "boom") n)))
        (send collector (sum ok (+ a b)))))))
(send w 0)
(+ (icell-get total) (icell-get never))
