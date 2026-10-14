;; => 100
;; A monitored worker that traps (an `int` divided by 0), not by `error`:
;; its watcher is sent the failure, whatever the machine says of it.
(define-type report (sumof (ok int) (failed string)))
(define total (icell int @c) (make-icell))
(define collector (addr report @p)
  (spawn (box report r)
    (tagcase (receive box)
      (ok v (icell-put! total v))
      (failed m (icell-put! total (if (string=? m "") 50 100))))))
(define* failed (subr pure (string) report) (lambda (m) (sum failed m)))
(define* answer (subr pure (int) report) (lambda (n) (sum ok (quotient 7 n))))
(define w (addr int @w)
  (spawn-monitored collector failed (box int r) (send collector (answer (receive box)))))
(send w 0)
(icell-get total)
