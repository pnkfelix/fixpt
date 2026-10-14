;; => 100
;; Both of a monitored process's branches fail: its watcher is sent one
;; failure, whichever came first, and the rest of the process is
;; cancelled; a second message, waited for 20 ms, does not come.
(define-type report (sumof (ok int) (failed string)))
(define total (icell int @c) (make-icell))
(define collector (addr report @p)
  (spawn (box report r)
    (tagcase (receive box)
      (ok v (icell-put! total v))
      (failed m
        (pselect ((receive box) x (icell-put! total 999))
                 ((sleep-until (i64+ (clock) (int->i64 20000000))) u (icell-put! total 100)))))))
(define* failed (subr pure (string) report) (lambda (m) (sum failed m)))
(define w (addr int @w)
  (spawn-monitored collector failed (box int r)
    (let ((n (receive box)))
      (par ((a (if (= n 0) (error "left") n)) (b (if (= n 0) (error "right") n)))
        (send collector (sum ok (+ a b)))))))
(send w 0)
(icell-get total)
