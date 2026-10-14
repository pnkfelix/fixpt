;; ! a deadlock
;; A monitored process fails while a `race` in it still runs: the race's
;; branches, which would count a billion each, are cancelled with the rest
;; of the process, so a wait for what no task will fill is found to be a
;; deadlock at once, not once they have counted.
(define-type report (sumof (ok int) (failed string)))
(define total (icell int @d) (make-icell))
(define never (icell int @e) (make-icell))
(define collector (addr report @p)
  (spawn (box report r)
    (tagcase (receive box)
      (ok v (icell-put! total v))
      (failed m (icell-put! total 100)))))
(define* failed (subr pure (string) report) (lambda (m) (sum failed m)))
(define* count (subr spin (int int) int)
  (lambda (i n) (if (= i n) i (count (+ i 1) n))))
(define w (addr int @w)
  (spawn-monitored collector failed (box int r)
    (let ((n (receive box)))
      (par ((a (race (count 0 1000000000) (count 1 1000000000)))
            (b (if (= n 0) (error "boom") n)))
        (send collector (sum ok (+ a b)))))))
(send w 0)
(+ (icell-get total) (icell-get never))
