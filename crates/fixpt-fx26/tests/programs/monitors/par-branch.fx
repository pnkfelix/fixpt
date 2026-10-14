;; => 100
;; A branch of `par` in a monitored process fails: the failure is the
;; process's, as `par`'s is the form's in a program, and its watcher is
;; sent it; the program goes on.
(define-type report (sumof (ok int) (failed string)))
(define total (icell int @c) (make-icell))
(define collector (addr report @p)
  (spawn (box report r)
    (tagcase (receive box)
      (ok v (icell-put! total v))
      (failed m (icell-put! total (if (string=? m "left") 100 50))))))
(define* failed (subr pure (string) report) (lambda (m) (sum failed m)))
(define w (addr int @w)
  (spawn-monitored collector failed (box int r)
    (let ((n (receive box)))
      (par ((a (if (= n 0) (error "left") n)) (b (* n 2)))
        (send collector (sum ok (+ a b)))))))
(send w 0)
(icell-get total)
